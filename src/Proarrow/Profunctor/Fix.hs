module Proarrow.Profunctor.Fix where

import Data.Functor.Const (Const (..))

import Proarrow.Core (Profunctor(..), PRO, Category (..), (:~>))
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Category.Instance.Nat (Nat(..))
import Proarrow.Profunctor.Composition ((:.:)(..))

type Fix :: PRO k k -> PRO k k
newtype Fix p a b where
  In :: { out :: (Fix p :.: p) a b } -> Fix p a b

instance Profunctor p => Profunctor (Fix p) where
  dimap l r = In . dimap l r . out \\ l \\ r
  r \\ In p = r \\ p

instance Functor Fix where
  map n@Prof{} = Prof (In . getProf (map n . getNat (map (map n))) . out)

cata :: (Profunctor p, Profunctor r) => (r :.: p :~> r) -> Fix p :~> r
cata alg = getProf go where go = Prof alg . getNat (map go) . Prof out

ana :: (Profunctor p, Profunctor r) => (r :~> r :.: p) -> r :~> Fix p
ana coalg = getProf go where go = Prof In . getNat (map go) . Prof coalg


data ListF x l = Nil | Cons x l
instance Functor (ListF x) where
  map _ Nil = Nil
  map f (Cons x l) = Cons x (f l)

embed :: ListF x [x] -> [x]
embed Nil = []
embed (Cons x xs) = x:xs

project :: [x] -> ListF x [x]
project [] = Nil
project (x:xs) = Cons x xs

embed' :: Star (Const [x]) :.: Star (ListF x) :~> Star (Const [x])
embed' (Star f :.: Star g) = Star (Const . embed . map (getConst . f) . g)

project' :: Star (Const [x]) :~> Star (Const [x]) :.: Star (ListF x)
project' (Star f) = Star Const :.: Star (project . getConst . f)

toList :: Fix (Star (ListF x)) :~> Star (Const [x])
toList = cata embed'

fromList :: Star (Const [x]) :~> Fix (Star (ListF x))
fromList = ana project'
