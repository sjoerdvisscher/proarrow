module Proarrow.Profunctor.Fix where

import Data.Functor.Const (Const (..))

import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (PRO, Profunctor (..), Promonad (..), (:~>))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Star (Star (..))

type Fix :: PRO k k -> PRO k k
newtype Fix p a b where
  In :: {out :: (p :.: Fix p) a b} -> Fix p a b

instance (Profunctor p) => Profunctor (Fix p) where
  dimap l r = In . dimap l r . out \\ l \\ r
  r \\ In p = r \\ p

instance Functor Fix where
  map n@Prof{} = Prof (In . unProf (unNat (map n) . map (map n)) . out)

hylo :: (Profunctor p, Profunctor a, Profunctor b) => (p :.: b :~> b) -> (a :~> p :.: a) -> a :~> b
hylo alg coalg = unProf go where go = Prof alg . map go . Prof coalg

cata :: (Profunctor p, Profunctor r) => (p :.: r :~> r) -> Fix p :~> r
cata alg = hylo alg out

ana :: (Profunctor p, Profunctor r) => (r :~> p :.: r) -> r :~> Fix p
ana coalg = hylo In coalg

data ListF x l = Nil | Cons x l
instance Functor (ListF x) where
  map _ Nil = Nil
  map f (Cons x l) = Cons x (f l)

embed :: ListF x [x] -> [x]
embed Nil = []
embed (Cons x xs) = x : xs

project :: [x] -> ListF x [x]
project [] = Nil
project (x : xs) = Cons x xs

embed' :: Star (ListF x) :.: Star (Const [x]) :~> Star (Const [x])
embed' (Star f :.: Star g) = Star (Const . embed . map (getConst . g) . f)

project' :: Star (Const [x]) :~> Star (ListF x) :.: Star (Const [x])
project' (Star f) = Star (project . getConst . f) :.: Star Const

toList :: Fix (Star (ListF x)) :~> Star (Const [x])
toList = cata embed'

fromList :: Star (Const [x]) :~> Fix (Star (ListF x))
fromList = ana project'
