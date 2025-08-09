{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Object.Copower where

import Data.Kind (Type)
import Prelude (type (~))

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CategoryOf (..), Ob, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Object.Power (Powered (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Enriched (Enriched, HomObj)
import Proarrow.Object.Exponential (Closed)

-- | Categories copowered over Hask.
class (Enriched v k, Closed v) => Copowered v k where
  type (n :: v) *. (a :: k) :: k
  withObCopower :: (Ob (a :: k), Ob (n :: v)) => ((Ob (n *. a)) => r) -> r
  copower :: (Ob (a :: k), Ob b) => n ~> HomObj v a b -> (n *. a) ~> b
  uncopower :: (Ob (a :: k), Ob n) => (n *. a) ~> b -> n ~> HomObj v a b

-- mapCobase :: forall {k} {v} (a :: k) b (n :: v). (Copowered v k, Ob n) => a ~> b -> n *. a ~> n *. b
-- mapCobase f = f // withObCopower @v @k @b @n (copower @v @k @a @(n *. b) @n (\n -> uncopower id n . f))

mapCopower :: forall {k} {v} (a :: k) (n :: v) m. (Copowered v k, Ob a) => (n ~> m) -> n *. a ~> m *. a
mapCopower f = withObCopower @v @k @a @m (copower @v @k @a @(m *. a) @n (uncopower @v @k @a id . f)) \\ f

instance Copowered Type Type where
  type n *. a = (n, a)
  withObCopower r = r
  copower f = \(n, a) -> f n a
  uncopower f n a = f (n, a)

instance Copowered Type () where
  type n *. a = '()
  withObCopower r = r
  copower _ = Unit
  uncopower Unit _ = Unit

instance (Copowered Type j, Copowered Type k) => Copowered Type (j, k) where
  type n *. '(a, b) = '(n *. a, n *. b)
  withObCopower @'(a, b) @n r = withObCopower @_ @j @a @n (withObCopower @_ @k @b @n r)
  copower f = copower (\n -> fstK (f n)) :**: copower (\n -> sndK (f n))
  uncopower (f :**: g) n = uncopower f n :**: uncopower g n

data (n :*.: p) a b where
  Copower :: n -> p a b -> (n :*.: p) a b
instance (Profunctor p) => Profunctor (n :*.: p) where
  dimap l r (Copower n p) = Copower n (dimap l r p)
  r \\ Copower _ p = r \\ p
instance (CategoryOf j, CategoryOf k) => Copowered Type (j +-> k) where
  type n *. a = n :*.: a
  withObCopower r = r
  copower f = Prof \(Copower n p) -> unProf (f n) p
  uncopower (Prof f) n = Prof \p -> f (Copower n p)

class (HomObj v (OP a) (OP b) ~ HomObj v b a) => HomObjOp v a b
instance (HomObj v (OP a) (OP b) ~ HomObj v b a) => HomObjOp v a b

instance (Copowered v k, Enriched v (OPPOSITE k), forall (a :: k) b. HomObjOp v a b) => Powered v (OPPOSITE k) where
  type OP a ^ n = OP (n *. a)
  withObPower @(OP a) @n r = withObCopower @v @k @a @n r
  power @(OP a) @(OP b) f = Op (copower @v @k @b @a f)
  unpower @(OP a) (Op f) = uncopower @v @k @a f

instance (Powered v k, Enriched v (OPPOSITE k), forall (a :: k) b. HomObjOp v a b) => Copowered v (OPPOSITE k) where
  type n *. OP a = OP (a ^ n)
  withObCopower @(OP a) @n r = withObPower @v @k @a @n r
  copower @(OP a) @(OP b) f = Op (power @v @k @b @a f)
  uncopower @(OP a) (Op f) = unpower @v @k @a f

