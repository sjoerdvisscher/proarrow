{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Instance.Arrow where

import Control.Arrow
  ( Arrow (..)
  , ArrowApply (..)
  , ArrowChoice (..)
  , ArrowLoop (..)
  , Kleisli (..)
  , (>>>)
  )
import Control.Category qualified as P
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
import Data.Kind (Type)
import Prelude (Either (..), Functor (..), Monad (..))

import Proarrow.Category.Monoidal (MonoidalProfunctor (..), Tensor)
import Proarrow.Category.Monoidal.Action (CoprodAction)
import Proarrow.Category.Monoidal.Distributive (DistributiveProfunctor)
import Proarrow.Category.Monoidal.Strength (Costrong (..), Strong (..))
import Proarrow.Colimit.BinaryCoproduct (Coprod (..), (++))
import Proarrow.Core (CAT, Profunctor (..), Promonad (..), rmap, type (+->))
import Proarrow.Functor (FromProfunctor (..))
import Proarrow.Limit.BinaryProduct ()
import Proarrow.Profunctor.Representable (Representable (..))

swap :: (b, a) -> (a, b)
swap ~(x, y) = (y, x)

type Arr :: CAT Type -> CAT Type
newtype Arr arr a b = Arr {unArr :: arr a b}

instance (Arrow arr) => Profunctor (Arr arr) where
  dimap l r (Arr a) = Arr (arr l >>> a >>> arr r)

instance (Arrow arr) => Promonad (Arr arr) where
  id = Arr (arr id)
  Arr f . Arr g = Arr (g >>> f)

instance (Arrow arr) => Strong Tensor (Arr arr) where
  act (Arr a) = Arr (second a)

instance (ArrowLoop arr) => Costrong Tensor (Arr arr) where
  coact (Arr f) = Arr (loop (arr swap >>> f >>> arr swap))

instance (Arrow arr) => MonoidalProfunctor (Arr arr) where
  one = Arr (arr id)
  Arr l ** Arr r = Arr (l *** r)

instance (ArrowChoice arr) => MonoidalProfunctor (Coprod (Arr arr)) where
  one = Coprod (Arr (arr id))
  Coprod (Arr l) ** Coprod (Arr r) = Coprod (Arr (l +++ r))

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

instance (Monad m) => Strong Tensor (Kleisli m) where
  act = second

instance (MonadPlus m) => Strong CoprodAction (Kleisli m) where
  act (Kleisli a) = Kleisli ((return . Left) ||| (a >>> fmap Right))

instance (MonadFix m) => Costrong Tensor (Kleisli m) where
  coact f = loop (arr swap >>> f >>> arr swap)

instance (Monad m) => MonoidalProfunctor (Kleisli m) where
  one = arr id
  l ** r = l *** r

instance (MonadPlus m) => MonoidalProfunctor (Coprod (Kleisli m)) where
  one = Coprod (Kleisli return)
  Coprod (Kleisli l) ** Coprod (Kleisli r) = Coprod (Kleisli ((l >>> fmap Left) ||| (r >>> fmap Right)))

instance (Functor m) => Representable (Kleisli m) where
  type Kleisli m % a = m a
  index = runKleisli
  tabulate = Kleisli
  repMap = fmap

instance (Promonad p) => P.Category (FromProfunctor p :: Type +-> Type) where
  id = id
  (.) = (.)

instance (MonoidalProfunctor p, Promonad p) => Arrow (FromProfunctor p :: Type +-> Type) where
  arr f = rmap f id
  FromProfunctor f *** FromProfunctor g = FromProfunctor (f ** g)

instance (DistributiveProfunctor p, Promonad p) => ArrowChoice (FromProfunctor p :: Type +-> Type) where
  FromProfunctor f +++ FromProfunctor g = FromProfunctor (f ++ g)

instance (Representable p, MonoidalProfunctor p, Promonad p) => ArrowApply (FromProfunctor p :: Type +-> Type) where
  app = FromProfunctor (tabulate \(FromProfunctor p, b) -> index p b)

instance (Costrong Tensor p, MonoidalProfunctor p, Promonad p) => ArrowLoop (FromProfunctor p :: Type +-> Type) where
  loop (FromProfunctor p) = FromProfunctor (coact @Tensor (dimap swap swap p))
