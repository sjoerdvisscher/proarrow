{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Sub where

import Data.Kind (Type)
import Prelude (($))

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

class IsOb (tag :: Type) a

type SUBCAT :: forall k. Type -> CAT k -> CAT k
type data SUBCAT tag kk i j = SUB (kk i j)
type instance UN SUB (SUB p) = p

type Sub :: CAT (SUBCAT ob kk i j)
data Sub a b where
  Sub :: (IsOb tag a, IsOb tag b) => a ~> b -> Sub (SUB a :: SUBCAT tag kk i j) (SUB b)

instance (Profunctor ((~>) :: CAT (kk i j))) => Profunctor (Sub :: CAT (SUBCAT tag kk i j)) where
  dimap = dimapDefault
  r \\ Sub p = r \\ p

instance (Promonad ((~>) :: CAT (kk i j))) => Promonad (Sub :: CAT (SUBCAT tag kk i j)) where
  id = Sub id
  Sub f . Sub g = Sub (f . g)

-- | The subcategory with objects with instances of the given constraint `IsOb tag`.
instance (CategoryOf (kk i j)) => CategoryOf (SUBCAT tag kk i j) where
  type (~>) = Sub
  type Ob (a :: SUBCAT tag kk i j) = (Is SUB a, Ob (UN SUB a), IsOb tag (UN SUB a))

class (IsOb tag (a `O` b)) => IsObO tag kk i j k (a :: kk i j) (b :: kk j k)
instance (IsOb tag (a `O` b)) => IsObO tag kk i j k (a :: kk i j) (b :: kk j k)

class (IsOb tag (I :: kk i i)) => IsObI tag kk i
instance (IsOb tag (I :: kk i i)) => IsObI tag kk i

instance
  ( Bicategory kk
  , forall i. (Ob0 kk i) => IsObI tag kk i
  , forall i j k (a :: kk i j) (b :: kk j k). (IsOb tag a, IsOb tag b) => IsObO tag kk i j k a b
  )
  => Bicategory (SUBCAT tag kk)
  where
  type Ob0 (SUBCAT tag kk) k = Ob0 kk k
  type I = SUB I
  type p `O` q = SUB (UN SUB p `O` UN SUB q)
  Sub m `o` Sub n = Sub $ m `o` n
  r \\\ Sub f = r \\\ f
  leftUnitor (Sub p) = Sub (leftUnitor p) \\\ p
  leftUnitorInv (Sub p) = Sub (leftUnitorInv p) \\\ p
  rightUnitor (Sub p) = Sub (rightUnitor p) \\\ p
  rightUnitorInv (Sub p) = Sub (rightUnitorInv p) \\\ p
  associator (Sub p) (Sub q) (Sub r) = Sub (associator p q r)
  associatorInv (Sub p) (Sub q) (Sub r) = Sub (associatorInv p q r)
