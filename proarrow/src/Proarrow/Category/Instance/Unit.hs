{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __terminal category__: the unit kind @()@ with its single object @'()@ and only the
-- identity arrow 'Unit'.
module Proarrow.Category.Instance.Unit where

import Data.Type.Equality (type (:~:) (..))
import Data.Type.Nat (Nat (..), SNat (..), snat)
import Prelude (Maybe (..), type (~))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin
  ( DecidableProfunctor (..)
  , Decision (..)
  , Enumerable (..)
  , Finite (..)
  , Indexed (..)
  , IndexedList (..)
  , ThinProfunctor (..)
  )
import Proarrow.Category.Instance.Bool (BOOL (..))
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

instance DecidableProfunctor Unit where
  type Holds Unit a b = TRU
  decide = Yes Unit
  toHolds Unit r = r

instance Indexed () where
  type Index '() = 'Z
  type At () 'Z = 'Just '()
  type At () ('S i) = 'Nothing

instance Finite () where
  type Objects () = '[ '()]
  finite = FCons FNil
  atLookup SZ = Refl
  atLookup SS = Refl

instance Enumerable () where
  withIndex r = r
  withOb @a r = case snat @(Index a) of SZ -> r
