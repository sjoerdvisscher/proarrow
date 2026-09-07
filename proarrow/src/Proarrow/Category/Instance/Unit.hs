{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __terminal category__: the unit kind @()@ with its single object @'()@ and only the
-- identity arrow 'Unit'.
module Proarrow.Category.Instance.Unit where

import Prelude (type (~))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin (ThinProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)

type Unit :: CAT ()
data Unit a b where
  Unit :: Unit '() '()

-- | The category with one object, the terminal category.
instance CategoryOf () where
  type (~>) = Unit
  type Ob a = a ~ '()

instance Promonad Unit where
  id = Unit
  Unit . Unit = Unit

instance Profunctor Unit where
  dimap = dimapDefault
  r \\ Unit = r

instance DaggerProfunctor Unit where
  dagger Unit = Unit

instance ThinProfunctor Unit where
  type HasArrow Unit a b = (a ~ b)
  arr = Unit
  withArr Unit r = r
