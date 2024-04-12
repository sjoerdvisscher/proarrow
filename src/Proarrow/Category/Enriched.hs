{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Enriched where

import Data.Kind (Constraint, Type)
import Prelude (($))

import Proarrow.Core (Promonad(..), CategoryOf(..), CAT, UN, Is, Kind)
import Proarrow.Category.Bicategory (Bicategory(O, I), Monad(..))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2(..), MonK(..))
import Proarrow.Object.BinaryProduct ()


type family V (vk :: k -> Type) :: CAT k
type family Arr (v :: CAT k) (a :: vk exta) (b :: vk extb) :: v exta extb
type (a :: vk exta) %~> (b :: vk extb) = Arr (V vk) a b

class (Bicategory (V vk)) => ECategory (vk :: k -> Type) where
  type EOb (a :: vk exta) :: Constraint
  eid :: EOb (a :: vk exta) => I ~> a %~> a
  ecomp :: (EOb (a :: vk exta), EOb (b :: vk extb), EOb (c :: vk extc))
        => ((a :: vk exta) %~> b) `O` (b %~> c) ~> a %~> c


type CATK :: Kind -> () -> Kind
data CATK k ext where
  CK :: k -> CATK k i
type instance UN CK (CK a) = a

type instance V (CATK k) = MonK Type
type instance Arr (MonK Type) (CK a) (CK b) = MK (a ~> b)

-- | A regular category as a Type-enriched category
instance CategoryOf k => ECategory (CATK k) where
  type EOb (a :: CATK k exta) = (Is CK a, Ob (UN CK a))
  eid = Mon2 $ \() -> id
  ecomp = Mon2 $ \(f, g) -> f . g


type MONADK :: forall {k} {kk} {a}. kk (a :: k) a -> k -> Type
data MONADK t ext where
  MDK :: () -> MONADK (t :: kk a a) exta

type instance V (MONADK (t :: kk a a)) = kk
type instance Arr kk (m :: MONADK (t :: kk a a) a) (n :: MONADK t a) = t

-- | A monad in a bicategory as a one object enriched category
instance Monad t => ECategory (MONADK (t :: kk a a)) where
  type EOb (m :: MONADK (t :: kk a a) exta) = (Is MDK m, exta ~ a)
  eid = eta
  ecomp = mu
