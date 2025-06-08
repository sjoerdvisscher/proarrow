{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Copower where

import Data.Kind (Type)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CategoryOf (..), Ob, Profunctor (..), Promonad (..), (//), type (+->))

-- | Categories copowered over Hask.
class (CategoryOf k) => Copowered k where
  type (n :: Type) *. (a :: k) :: k
  withObCopower :: (Ob (a :: k)) => ((Ob (n *. a)) => r) -> r
  copower :: (Ob (a :: k), Ob b) => (n -> a ~> b) -> (n *. a) ~> b
  uncopower :: (Ob (a :: k)) => (n *. a) ~> b -> n -> a ~> b

mapCobase :: forall k a b n. (Copowered k) => (a :: k) ~> b -> n *. a ~> n *. b
mapCobase f = f // withObCopower @k @b @n (copower @k @a @(n *. b) @n (\n -> uncopower id n . f))

mapCopower :: forall k a n m. (Copowered k, Ob (a :: k)) => (n -> m) -> n *. a ~> m *. a
mapCopower f = withObCopower @k @a @m (copower @k @a @(m *. a) @n (\m -> uncopower id (f m)))

instance Copowered Type where
  type n *. a = (n, a)
  withObCopower r = r
  copower f = \(n, a) -> f n a
  uncopower f n a = f (n, a)

instance Copowered () where
  type n *. a = '()
  withObCopower r = r
  copower _ = Unit
  uncopower Unit _ = Unit

instance (Copowered j, Copowered k) => Copowered (j, k) where
  type (n :: Type) *. '(a, b) = '(n *. a, n *. b)
  withObCopower @'(a, b) @n r = withObCopower @j @a @n (withObCopower @k @b @n r)
  copower f = copower @j (\n -> fstK (f n)) :**: copower @k (\n -> sndK (f n))
  uncopower (f :**: g) n = uncopower f n :**: uncopower g n

data (n :*.: p) a b where
  Copower :: n -> p a b -> (n :*.: p) a b
instance (Profunctor p) => Profunctor (n :*.: p) where
  dimap l r (Copower n p) = Copower n (dimap l r p)
  r \\ Copower _ p = r \\ p
instance (CategoryOf j, CategoryOf k) => Copowered (j +-> k) where
  type n *. a = n :*.: a
  withObCopower r = r
  copower f = Prof \(Copower n p) -> unProf (f n) p
  uncopower (Prof f) n = Prof \p -> f (Copower n p)
