{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Power where

import Data.Kind (Type)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CategoryOf (..), Ob, Profunctor (..), Promonad (..), (//), type (+->))

-- | Categories powered over Hask.
class (CategoryOf k) => Powered k where
  type (a :: k) ^ (n :: Type) :: k
  withObPower :: (Ob (a :: k)) => ((Ob (a ^ n)) => r) -> r
  power :: (Ob (a :: k), Ob b) => (n -> a ~> b) -> a ~> (b ^ n)
  unpower :: (Ob (b :: k)) => a ~> (b ^ n) -> n -> a ~> b

mapBase :: forall k a b n. (Powered k) => (a :: k) ~> b -> a ^ n ~> b ^ n
mapBase f = f // withObPower @k @a @n (power @k @(a ^ n) @b @n (\n -> f . unpower id n))

mapPower :: forall k a n m. (Powered k, Ob (a :: k)) => (n -> m) -> a ^ m ~> a ^ n
mapPower f = withObPower @k @a @m (power @k @(a ^ m) @a @n (\n -> unpower id (f n)))

instance Powered Type where
  type a ^ n = n -> a
  withObPower r = r
  power f a n = f n a
  unpower f n a = f a n

instance Powered () where
  type a ^ n = '()
  withObPower r = r
  power _ = Unit
  unpower Unit _ = Unit

instance (Powered j, Powered k) => Powered (j, k) where
  type '(a, b) ^ n = '(a ^ n, b ^ n)
  withObPower @'(a, b) @n r = withObPower @j @a @n (withObPower @k @b @n r)
  power f = power @j (\n -> fstK (f n)) :**: power @k (\n -> sndK (f n))
  unpower (f :**: g) n = unpower f n :**: unpower g n

data (p :^: n) a b where
  Power :: (Ob a, Ob b) => {unPower :: n -> p a b} -> (p :^: n) a b
instance (Profunctor p) => Profunctor (p :^: n) where
  dimap l r (Power f) = l // r // Power \n -> dimap l r (f n)
  r \\ Power{} = r
instance (CategoryOf j, CategoryOf k) => Powered (j +-> k) where
  type a ^ n = a :^: n
  withObPower r = r
  power f = Prof \p -> p // Power \n -> unProf (f n) p
  unpower (Prof f) n = Prof \p -> unPower (f p) n