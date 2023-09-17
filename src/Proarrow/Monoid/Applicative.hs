{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Monoid.Applicative where

import Data.Kind (Constraint)
import Data.Function (($))

import Proarrow.Core (type (~>), Category(..), (//))
import Proarrow.Functor (Functor)
import Proarrow.Object.Terminal (El)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..), HasCoproducts, CoproductFunctor)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts, ProductFunctor)
import Proarrow.Monoid (Monoid(..))
import Proarrow.Profunctor.Day (Day(..), DayUnit(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Category.Instance.Prof (Prof(..))

type Applicative :: forall {j} {k}. (j -> k) -> Constraint
class (HasProducts j, HasProducts k, Functor f) => Applicative (f :: j -> k) where
  pure :: El a -> El (f a)
  liftA2 :: (a && b ~> c) -> f a && f b ~> f c

type Alternative :: forall {j} {k}. (j -> k) -> Constraint
class (HasCoproducts j, HasProducts k, Functor f) => Alternative (f :: j -> k) where
  empty :: El (f a)
  alt :: (a || b ~> c) -> f a && f b ~> f c

instance (HasProducts j, HasProducts k) => Monoid (Applicative f) (Star (f :: j -> k)) where
  type Ten (Applicative f) = Star (Day ProductFunctor ProductFunctor)
  mult = Prof $ \(Day (Star @x @b bfx) (Star @y cfy) abc xyz) ->
    xyz // Star $ liftA2 @f @x @y xyz . (bfx *** cfy) . abc
  unit = Prof $ \(DayUnit a x) -> x // Star $ pure x . a

instance (HasCoproducts j, HasProducts k) => Monoid (Alternative f) (Star (f :: j -> k)) where
  type Ten (Alternative f) = Star (Day ProductFunctor CoproductFunctor)
  mult = Prof $ \(Day (Star @x @b bfx) (Star @y cfy) abc xyz) ->
    xyz // Star $ alt @f @x @y xyz . (bfx *** cfy) . abc
  unit = Prof $ \(DayUnit a x) -> x // Star $ empty . a