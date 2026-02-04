{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Arrow where

import Control.Arrow
  ( Arrow (..)
  , ArrowApply (..)
  , ArrowChoice (..)
  , ArrowLoop (..)
  , ArrowZero (..)
  , Kleisli (..)
  , (>>>)
  )
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
import Data.Kind (Type)
import Prelude (Either (..), Functor (..), Monad (..))

import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (Costrong (..), Strong (..))
import Proarrow.Core (CAT, Profunctor (..), Promonad (..))
import Proarrow.Object.BinaryCoproduct (COPROD, Coprod (..))
import Proarrow.Object.BinaryProduct ()
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))

type Arr :: CAT Type -> CAT Type
newtype Arr arr a b = Arr {unArr :: arr a b}

instance (Arrow arr) => Profunctor (Arr arr) where
  dimap l r (Arr a) = Arr (arr l >>> a >>> arr r)

instance (Arrow arr) => Promonad (Arr arr) where
  id = Arr (arr id)
  Arr f . Arr g = Arr (g >>> f)

instance (Arrow arr) => Strong Type (Arr arr) where
  act f (Arr a) = Arr (arr f *** a)

instance (ArrowLoop arr) => Costrong Type (Arr arr) where
  coact (Arr f) = Arr (loop (arr swap >>> f >>> arr swap))
    where
      swap ~(x, y) = (y, x)

instance (Arrow arr) => MonoidalProfunctor (Arr arr) where
  par0 = Arr (arr id)
  Arr l `par` Arr r = Arr (l *** r)

instance (ArrowChoice arr) => MonoidalProfunctor (Coprod (Arr arr)) where
  par0 = Coprod (Arr (arr id))
  Coprod (Arr l) `par` Coprod (Arr r) = Coprod (Arr (l +++ r))

instance (ArrowApply arr) => Representable (Arr arr) where
  type Arr arr % a = arr () a
  index (Arr a) b = arr (\() -> b) >>> a
  tabulate f = Arr (arr (\a -> (f a, ())) >>> app)
  repMap f a = a >>> arr f

instance (Functor m) => Profunctor (Kleisli m) where
  dimap l r (Kleisli a) = Kleisli (fmap r . a . l)

instance (Monad m) => Promonad (Kleisli m) where
  id = arr id
  f . g = g >>> f

instance (Monad m) => Strong Type (Kleisli m) where
  act f a = arr f *** a

instance (MonadPlus m) => Strong (COPROD Type) (Kleisli m) where
  act (Coprod (Id f)) (Kleisli a) = Kleisli ((f >>> (return . Left)) ||| (a >>> fmap Right))

instance (MonadFix m) => Costrong Type (Kleisli m) where
  coact f = loop (arr swap >>> f >>> arr swap)
    where
      swap ~(x, y) = (y, x)

instance (Monad m) => MonoidalProfunctor (Kleisli m) where
  par0 = arr id
  l `par` r = l *** r

instance (MonadPlus m) => MonoidalProfunctor (Coprod (Kleisli m)) where
  par0 = Coprod zeroArrow
  Coprod (Kleisli l) `par` Coprod (Kleisli r) = Coprod (Kleisli ((l >>> fmap Left) ||| (r >>> fmap Right)))

instance (Functor m) => Representable (Kleisli m) where
  type Kleisli m % a = m a
  index = runKleisli
  tabulate = Kleisli
  repMap = fmap
