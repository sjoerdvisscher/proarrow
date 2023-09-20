module Proarrow.Profunctor.Fix where

import Data.Kind (Type)

import Proarrow.Core (Profunctor(..), PRO, lmap, rmap, type (~>), Category (..), CategoryOf)
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Category.Opposite (OP(..), Op (..))
import Proarrow.Category.Instance.Nat (Nat(..))
import Proarrow.Object.Terminal (El)


type Fix' :: PRO k k -> OP k -> Type
data Fix' p a where
  In :: p a b -> Fix p b -> Fix p a

type Fix p a = Fix' p ('OP a)

instance Profunctor p => Functor (Fix' p) where
  map (Op f) (In p fp) = In (lmap f p) fp

instance Functor Fix' where
  map (Prof n) = Nat \(In p fp) -> In (n p) (getNat (map (Prof n)) fp) \\ p


cata :: Profunctor p => (forall a. p a b -> a ~> b) -> Fix p c -> c ~> b
cata alg (In f ff) = alg (rmap (cata alg ff) f)

ana :: CategoryOf k => (forall (a :: k). (a ~> b) -> p a b) -> (c ~> b) -> Fix p c
ana coalg f = In (coalg f) (ana coalg id) \\ f


data ListF x l = Nil | Cons x l
instance Functor (ListF x) where
  map _ Nil = Nil
  map f (Cons x l) = Cons x (f l)

project :: [x] -> ListF x [x]
project [] = Nil
project (x:xs) = Cons x xs

embed :: ListF x [x] -> [x]
embed Nil = []
embed (Cons x xs) = x:xs

project' :: (a ~> [x]) -> Star (ListF x) a [x]
project' = Star . (project .)

embed' :: Star (ListF x) a [x] -> a ~> [x]
embed' = (embed .) . getStar

toList :: Fix (Star (ListF x)) () -> El [x]
toList = cata embed'

fromList :: El [x] -> Fix (Star (ListF x)) ()
fromList = ana project'
