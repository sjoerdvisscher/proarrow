{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Enriched where

import Data.Kind (Constraint, Type)
import Prelude (($), type (~))

import Proarrow.Category.Bicategory (Bicategory (I, O), Monad (..))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Promonad (..), UN)
import Proarrow.Object.BinaryProduct ()
-- import Proarrow.Preorder (PreorderOf(..), CPromonad(..), (\\), POS)
-- import Proarrow.Category.Instance.PreorderAsCategory (POCATK(..), PoAsCat (..))

type family V (vk :: k -> Type) :: CAT k
type family Arr (v :: CAT k) (a :: vk exta) (b :: vk extb) :: v exta extb
type (a :: vk exta) %~> (b :: vk extb) = Arr (V vk) a b

class (Bicategory (V vk)) => ECategory (vk :: k -> Type) where
  type EOb (a :: vk exta) :: Constraint
  eid :: (EOb (a :: vk exta)) => I ~> a %~> a
  ecomp
    :: (EOb (a :: vk exta), EOb (b :: vk extb), EOb (c :: vk extc))
    => ((b :: vk extb) %~> c) `O` (a %~> b) ~> a %~> c

type CATK :: Kind -> () -> Kind
data CATK k ext where
  CK :: k -> CATK k i
type instance UN CK (CK a) = a

type instance V (CATK k) = MonK Type
type instance Arr (MonK Type) (CK a) (CK b) = MK (a ~> b)

-- | A regular category as a Type-enriched category
instance (CategoryOf k) => ECategory (CATK k) where
  type EOb (a :: CATK k exta) = (Is CK a, Ob (UN CK a))
  eid = Mon2 $ \() -> id
  ecomp = Mon2 $ \(f, g) -> g . f

-- type POSK :: Kind -> () -> Kind
-- data POSK k ext where
--   PK :: k -> POSK k i
-- type instance UN PK (PK a) = a

-- type instance V (POSK k) = MonK (POCATK Constraint)
-- type instance Arr (MonK (POCATK Constraint)) a b = MK (PC (UN PK a <= UN PK b))

-- -- | A poset as a Constraint-enriched category
-- instance (PreorderOf k) => ECategory (POSK k) where
--   type EOb (a :: POSK k exta) = (Is PK a, COb (UN PK a))
--   eid @_ @a = Mon2 $ PoAsCat \\ (cid @((<=) :: POS k) @(UN PK a))
--   ecomp @_ @a @_ @b @_ @c = Mon2 $ _ -- PoAsCat \\ (ccomp @((<=) :: POS k) @(UN PK a) @(UN PK b) @(UN PK c))


type MONADK :: forall {k} {kk} {a}. kk (a :: k) a -> k -> Type
data MONADK t ext where
  MDK :: () -> MONADK (t :: kk a a) exta

type instance V (MONADK (t :: kk a a)) = kk
type instance Arr kk (m :: MONADK (t :: kk a a) a) (n :: MONADK t a) = t

-- | A monad in a bicategory as a one object enriched category
instance (Monad t) => ECategory (MONADK (t :: kk a a)) where
  type EOb (m :: MONADK (t :: kk a a) exta) = (Is MDK m, exta ~ a)
  eid = eta
  ecomp = mu
