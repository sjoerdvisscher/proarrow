module Proarrow.Category.Instance.Free where

import Data.Kind (Type)

import Proarrow.Core (CAT, UN, Is, CategoryOf(..), Promonad(..), Profunctor(..), (:~>), dimapDefault)


infixr 4 :|

newtype FREE (g :: k -> k -> Type) = F k
type instance UN F (F k) = k

type Free :: CAT (FREE g)
data Free a b where
  FreeId :: Free (F a) (F a)
  (:|) :: g a b -> Free (F b :: FREE g) (F c) -> Free (F a :: FREE g) (F c)

class Rewrite g where
  rewriteAfterCons :: (Free :: CAT (FREE g)) :~> (Free :: CAT (FREE g))

instance Rewrite g => CategoryOf (FREE g) where
  type (~>) = Free
  type Ob a = Is F a

instance Rewrite g => Promonad (Free :: CAT (FREE g)) where
  id = FreeId
  FreeId . a = a
  a . FreeId = a
  a . (g :| b) = rewriteAfterCons (g :| (a . b)) \\ a

instance Rewrite g => Profunctor (Free :: CAT (FREE g)) where
  dimap = dimapDefault
  r \\ FreeId = r
  r \\ _ :| _ = r
