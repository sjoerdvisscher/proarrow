{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Promonad
  ( Promonad (..)
  , Procomonad (..)
  ) where

import Proarrow.Core (CAT, CategoryOf, Profunctor, Promonad (..), src, (:~>), type (~>))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))

class (Profunctor p) => Procomonad p where
  extract :: p :~> (~>)
  duplicate :: p :~> p :.: p

instance (CategoryOf k) => Procomonad (Id :: CAT k) where
  extract (Id f) = f
  duplicate (Id f) = Id (src f) :.: Id f
