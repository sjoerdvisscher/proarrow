{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Sub where

import Data.Kind (Constraint, Type)
import Prelude (($))

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type family IsOb (tag :: Type) (a :: kk i j) :: Constraint
type family IsOb0 (tag :: Type) (k :: s) :: Constraint

type SUBCAT :: forall {s}. Type -> CAT s -> CAT s
type data SUBCAT tag kk i j = SUB (kk i j)
type instance UN SUB (SUB p) = p

type Sub :: CAT (SUBCAT ob kk i j)
data Sub a b where
  Sub :: forall {i} {j} {tag} {kk} a b
     . (IsOb tag a, IsOb tag b, IsOb0 tag i, IsOb0 tag j) => a ~> b -> Sub (SUB a :: SUBCAT tag kk i j) (SUB b)

instance (Profunctor ((~>) :: CAT (kk i j))) => Profunctor (Sub :: CAT (SUBCAT tag kk i j)) where
  dimap = dimapDefault
  r \\ Sub p = r \\ p

instance (Promonad ((~>) :: CAT (kk i j))) => Promonad (Sub :: CAT (SUBCAT tag kk i j)) where
  id = Sub id
  Sub f . Sub g = Sub (f . g)

-- | The subcategory with objects with instances of the given constraint `IsOb tag`.
instance (CategoryOf (kk i j)) => CategoryOf (SUBCAT tag kk i j) where
  type (~>) = Sub
  type Ob (a :: SUBCAT tag kk i j) = (Is SUB a, Ob (UN SUB a), IsOb tag (UN SUB a), IsOb0 tag i, IsOb0 tag j)

class WithObO2 tag kk where
  withObO2
    :: forall {i} {j} {k} (a :: kk j k) (b :: kk i j) r. (Ob a, Ob b, IsOb tag a, IsOb tag b) => ((IsOb tag (a `O` b), Ob (a `O` b)) => r) -> r

class (IsOb tag (I :: kk i i)) => IsObI tag kk i
instance (IsOb tag (I :: kk i i)) => IsObI tag kk i

instance
  ( Bicategory kk
  , forall i. (Ob0 kk i) => IsObI tag kk i
  , WithObO2 tag kk
  )
  => Bicategory (SUBCAT tag kk)
  where
  type Ob0 (SUBCAT tag kk) k = (Ob0 kk k, IsOb0 tag k)
  type I = SUB I
  type p `O` q = SUB (UN SUB p `O` UN SUB q)
  withOb2 @(SUB a) @(SUB b) r = withOb2 @kk @a @b (withObO2 @tag @kk @a @b r)
  withOb0s @(SUB a) r = withOb0s @kk @a r
  Sub @a @b m `o` Sub @c @d n = withObO2 @tag @kk @a @c (withObO2 @tag @kk @b @d (Sub (m `o` n))) \\\ m \\\ n
  r \\\ Sub f = r \\\ f
  leftUnitor @(SUB a) = withObO2 @tag @kk @I @a $ Sub leftUnitor
  leftUnitorInv @(SUB a) = withObO2 @tag @kk @I @a $ Sub leftUnitorInv
  rightUnitor @(SUB a) = withObO2 @tag @kk @a @I $ Sub rightUnitor
  rightUnitorInv @(SUB a) = withObO2 @tag @kk @a @I $ Sub rightUnitorInv
  associator @(SUB p) @(SUB q) @(SUB r) =
    withObO2 @tag @kk @p @q $
      withObO2 @tag @kk @q @r $
        withObO2 @tag @kk @(p `O` q) @r $
          withObO2 @tag @kk @p @(q `O` r) $
            Sub $
              associator @kk @p @q @r
  associatorInv @(SUB p) @(SUB q) @(SUB r) =
    withObO2 @tag @kk @p @q $
      withObO2 @tag @kk @q @r $
        withObO2 @tag @kk @(p `O` q) @r $
          withObO2 @tag @kk @p @(q `O` r) $
            Sub $
              associatorInv @kk @p @q @r