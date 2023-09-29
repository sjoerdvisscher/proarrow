module Proarrow.Category.Instance.Free where

import Data.Kind (Type)

import Proarrow.Core (CAT, Category(..), Profunctor(..), (:~>), type (~>), dimapDefault)

infixr 4 :|

newtype FREE (g :: k -> k -> Type) = F k
type family UNF (a :: FREE g) where UNF (F k) = k

type Free :: CAT (FREE g)
data Free a b where
  FreeId :: Free (F a) (F a)
  (:|) :: g a b -> Free (F b :: FREE g) (F c) -> Free (F a :: FREE g) (F c)

class Rewrite g where
  rewriteAfterCons :: (Free :: CAT (FREE g)) :~> (Free :: CAT (FREE g))

type instance (~>) = Free
instance Rewrite g => Category (Free :: CAT (FREE g)) where
  type Ob a = a ~ F (UNF a)
  id = FreeId
  FreeId . a = a
  a . FreeId = a
  a . (g :| b) = rewriteAfterCons (g :| (a . b)) \\ a

instance Rewrite g => Profunctor (Free :: CAT (FREE g)) where
  dimap = dimapDefault
  r \\ FreeId = r
  r \\ _ :| _ = r
