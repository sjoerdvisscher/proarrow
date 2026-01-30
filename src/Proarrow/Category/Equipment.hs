{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Category.Equipment
  ( Equipment (..)
  , TightAdjoint
  , CotightAdjoint
  , Tight
  , Cotight
  , IsCotight
  , IsTight
  , IsOb
  , WithObO2 (..)
  , TightPair
  ) where

import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..))
import Proarrow.Category.Bicategory.Sub (IsOb, IsOb0, SUBCAT, WithObO2 (..))
import Proarrow.Core (Any, CategoryOf (..))

type data Tight
type data Cotight

type instance IsOb0 Tight k = Any k
type instance IsOb0 Cotight k = Any k

class (IsOb Tight f, Ob f) => IsTight f
instance (IsOb Tight f, Ob f) => IsTight f
class (IsOb Cotight f, Ob f) => IsCotight f
instance (IsOb Cotight f, Ob f) => IsCotight f

type family CotightAdjoint (p :: kk j i) :: kk i j
type family TightAdjoint (p :: kk j i) :: kk i j

class
  ( Bicategory kk
  , Bicategory (SUBCAT Tight kk)
  , Bicategory (SUBCAT Cotight kk)
  , WithObO2 Cotight kk
  , WithObO2 Tight kk
  ) =>
  Equipment kk
  where
  withCotightAdjoint
    :: forall {j} {k} (f :: kk j k) r. (IsTight f) => ((Adjunction f (CotightAdjoint f), IsCotight (CotightAdjoint f)) => r) -> r
  withTightAdjoint
    :: forall {j} {k} (f :: kk j k) r. (IsCotight f) => ((Adjunction (TightAdjoint f) f, IsTight (TightAdjoint f)) => r) -> r

class (IsTight f, IsCotight g, Adjunction f g) => TightPair f g
instance (IsTight f, IsCotight g, Adjunction f g) => TightPair f g
