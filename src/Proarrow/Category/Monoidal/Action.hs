{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Action where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj, type (+->))

-- | Profuntorial strength for a monoidal action.
-- Gives functorial strength for Star, and functorial costrength for Costar.
type Strong :: forall {j} {k}. Kind -> j +-> k -> Constraint
class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Strong m (p :: c +-> d) where
  act :: forall (a :: m) b x y. a ~> b -> p x y -> p (Act a x) (Act b y)

class (Monoidal m, CategoryOf k, Strong m ((~>) :: CAT k)) => MonoidalAction m k where
  -- I would like to default Act to `**`, but that doesn't seem possible without GHC thinking `m` and `k` are the same.
  type Act (a :: m) (x :: k) :: k
  withObAct :: (Ob (a :: m), Ob (x :: k)) => ((Ob (Act a x)) => r) -> r
  unitor :: (Ob (x :: k)) => Act (Unit :: m) x ~> x
  unitorInv :: (Ob (x :: k)) => x ~> Act (Unit :: m) x
  multiplicator :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act a (Act b x) ~> Act (a ** b) x
  multiplicatorInv :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act (a ** b) x ~> Act a (Act b x)

class (Act a b ~ a ** b) => ActIsTensor a b
instance (Act a b ~ a ** b) => ActIsTensor a b
class (Act a (Act b c) ~ a ** (b ** c), a ** (Act b c) ~ a ** (b ** c), Act a (b ** c) ~ a ** (b ** c)) => ActIsTensor3 a b c
instance (Act a (Act b c) ~ a ** (b ** c), a ** (Act b c) ~ a ** (b ** c), Act a (b ** c) ~ a ** (b ** c)) => ActIsTensor3 a b c
class
  ( MonoidalAction k k
  , SymMonoidal k
  , forall (a :: k) (b :: k). ActIsTensor a b
  , forall (a :: k) (b :: k) (c :: k). ActIsTensor3 a b c
  ) =>
  SelfAction k
instance
  ( MonoidalAction k k
  , SymMonoidal k
  , forall (a :: k) (b :: k). ActIsTensor a b
  , forall (a :: k) (b :: k) (c :: k). ActIsTensor3 a b c
  )
  => SelfAction k

toSelfAct :: forall {k} (a :: k) b. (SelfAction k, Ob a, Ob b) => a ** b ~> Act a b
toSelfAct = obj @a `act` obj @b

fromSelfAct :: forall {k} (a :: k) b. (SelfAction k, Ob a, Ob b) => Act a b ~> a ** b
fromSelfAct = obj @a `act` obj @b

composeActs
  :: forall {m} {k} (x :: m) y (c :: k) a b
   . (MonoidalAction m k, Ob x, Ob y, Ob c)
  => a ~> Act x b
  -> b ~> Act y c
  -> a ~> Act (x ** y) c
composeActs f g = multiplicator @m @k @x @y @c . act (obj @x) g . f

decomposeActs
  :: forall {m} {k} (x :: m) y (c :: k) a b
   . (MonoidalAction m k, Ob x, Ob y, Ob c)
  => Act y c ~> b
  -> Act x b ~> a
  -> Act (x ** y) c ~> a
decomposeActs f g = g . act (obj @x) f . multiplicatorInv @m @k @x @y @c

first' :: forall {k} {p :: CAT k} c a b. (SelfAction k, Strong k p, Ob c) => p a b -> p (a ** c) (b ** c)
first' p = dimap (swap @k @a @c) (swap @k @c @b) (second' @c p) \\ p

second' :: forall {k} {p :: CAT k} c a b. (SelfAction k, Strong k p, Ob c) => p a b -> p (c ** a) (c ** b)
second' p = act (obj @c) p

-- | This is not monoidal `par` but premonoidal, i.e. no sliding.
-- So with `prepar f g` the effects of f happen before the effects of g.
-- p needs to be a commutative promonad for this to be monoidal `par`.
prepar :: forall {k} {p :: CAT k} a b c d. (SelfAction k, Strong k p, Promonad p) => p a b -> p c d -> p (a ** c) (b ** d)
prepar f g = second' @b g . first' @c f \\ f \\ g

strongPar0 :: forall {k} {p :: CAT k} a. (SelfAction k, Strong k p, MonoidalProfunctor p, Ob a) => p a a
strongPar0 = dimap rightUnitorInv rightUnitor (act (obj @a) par0)

type Costrong :: forall {j} {k}. Kind -> j +-> k -> Constraint
class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Costrong m (p :: c +-> d) where
  coact :: forall (a :: m) x y. (Ob a, Ob x, Ob y) => p (Act a x) (Act a y) -> p x y

trace :: forall {k} (p :: k +-> k) u x y. (SelfAction k, Costrong k p, Ob x, Ob y, Ob u) => p (x ** u) (y ** u) -> p x y
trace p = coact @k @p @u @x @y (dimap (swap @k @u @x) (swap @k @y @u) p) \\ p

class (SelfAction k, Costrong k ((~>) :: CAT k), SymMonoidal k) => TracedMonoidal k
instance (SelfAction k, Costrong k ((~>) :: CAT k), SymMonoidal k) => TracedMonoidal k
