{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Strength where

import Data.Kind (Constraint)

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal.Action (Act, CoprodAction, MonoidalAction, actHom)
import Proarrow.Colimit.BinaryCoproduct (COPROD (..), HasBinaryCoproducts (..), swapCoprod)
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepUniv)
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Representable (Representable (..), repUniv)

-- | Profuntorial strength for a monoidal actions.
-- Gives functorial strength for representable profunctors,
-- and functorial costrength for corepresentable profunctors.
type Strong :: forall {m} {k}. (m, k) +-> k -> k +-> k -> Constraint
class (MonoidalAction t, Profunctor p) => Strong t p where
  act :: (Ob a) => p x y -> p (Act t a x) (Act t a y)

instance (Strong t p, Strong t q) => Strong t (p :*: q) where
  act @a (p :*: q) = act @t @_ @a p :*: act @t @_ @a q

instance (Strong t p, Strong t q) => Strong t (p :+: q) where
  act @a (InjL p) = InjL (act @t @_ @a p)
  act @a (InjR q) = InjR (act @t @_ @a q)

instance (MonoidalAction t) => Strong t (Id :: CAT k) where
  act @a (Id g) = Id (actHom @t (obj @a) g)

type MonStrong (p :: k +-> k) = (Strong Tensor p, SymMonoidal k)

-- | If a strong profunctor is representable, we get the usual strength for the representing functor.
strength
  :: forall {m} t p a b. (Representable p, Strong t p, Ob (a :: m), Ob b) => Act t a (p % b) ~> p % Act t a b
strength = index (act @t @p @a (repUniv @p @b))

-- | If a strong profunctor is corepresentable, we get the usual costrength for the representing functor.
costrength
  :: forall {m} t p a b. (Corepresentable p, Strong t p, Ob (a :: m), Ob b) => p %% Act t a b ~> Act t a (p %% b)
costrength = coindex (act @t @p @a (corepUniv @p @b))

first'
  :: forall {k} {p :: k +-> k} c a b. (MonStrong p, Ob c) => p a b -> p (a ** c) (b ** c)
first' p = dimap (swap @k @a @c) (swap @k @c @b) (second' @c p) \\ p

second'
  :: forall {k} {p :: k +-> k} c a b. (MonStrong p, Ob c) => p a b -> p (c ** a) (c ** b)
second' p = act @Tensor @p @c p

left'
  :: forall {k} (p :: k +-> k) c a b. (Strong CoprodAction p, HasBinaryCoproducts k, Ob c) => p a b -> p (a || c) (b || c)
left' p = dimap (swapCoprod @a @c) (swapCoprod @c @b) (right' @_ @c p) \\ p

right' :: forall {k} (p :: k +-> k) c a b. (Strong CoprodAction p, Ob c) => p a b -> p (c || a) (c || b)
right' p = act @CoprodAction @p @(COPR c) p

-- | This is not monoidal ** but premonoidal, i.e. no sliding.
-- So with `premon f g` the effects of f happen before the effects of g.
-- p needs to be a commutative promonad for this to be monoidal **.
premon
  :: forall {k} {p :: CAT k} a b c d. (MonStrong p, Promonad p) => p a b -> p c d -> p (a ** c) (b ** d)
premon f g = second' @b g . first' @c f \\ f \\ g

strongId :: forall {k} {p :: k +-> k} a. (MonStrong p, MonoidalProfunctor p, Ob a) => p a a
strongId = dimap rightUnitorInv rightUnitor (second' @a one)

-- | A monoidal promonad is automatically strong.
monActDefault :: forall {p} a x y. (MonoidalProfunctor p, Promonad p, Ob a) => p x y -> p (a ** x) (a ** y)
monActDefault p = id @p @a ** p

type Costrong :: forall {m} {k}. (m, k) +-> k -> k +-> k -> Constraint
class (MonoidalAction t, Profunctor p) => Costrong t p where
  coact :: forall a x y. (Ob a, Ob x, Ob y) => p (Act t a x) (Act t a y) -> p x y

instance Costrong Tensor (->) where
  coact f x = let (u, y) = f (u, x) in y

instance (MonoidalAction t, Costrong t (Hom k)) => Costrong t (Id :: CAT k) where
  coact @a (Id g) = Id (coact @t @(Hom k) @a g)

trace
  :: forall {k} (p :: k +-> k) u x y
   . (Costrong Tensor p, Ob x, Ob y, Ob u, SymMonoidal k) => p (x ** u) (y ** u) -> p x y
trace p = coact @Tensor @p @u @x @y (dimap (swap @k @u @x) (swap @k @y @u) p) \\ p

class (Costrong Tensor (Hom k), SymMonoidal k) => TracedMonoidal k
instance (Costrong Tensor (Hom k), SymMonoidal k) => TracedMonoidal k
