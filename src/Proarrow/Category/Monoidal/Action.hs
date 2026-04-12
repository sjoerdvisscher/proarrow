{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Action where

import Data.Kind (Constraint, Type)
import Prelude (type (~))

import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj, type (+->), OB, UN)
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep)
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), trivialRep)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..), SubMonoidal)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))

-- | Profuntorial strength for a monoidal action.
-- Gives functorial strength for representable profunctors,
-- and functorial costrength for corepresentable profunctors.
type Strong :: forall {j} {k}. Kind -> j +-> k -> Constraint
class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Strong m (p :: c +-> d) where
  act :: forall (a :: m) b x y. a ~> b -> p x y -> p (Act a x) (Act b y)

class (Monoidal m, CategoryOf k, Strong m ((~>) :: CAT k)) => MonoidalAction m k where
  -- I would like to default Act to `**`, but that doesn't seem possible without GHC thinking `m` and `k` are the same.
  type Act (a :: m) (x :: k) :: k
  withObAct :: (Ob (a :: m), Ob (x :: k)) => ((Ob (Act a x)) => r) -> r
  unitor :: (Ob (x :: k)) => Act (Unit :: m) x ~> x
  unitorInv :: (Ob (x :: k)) => x ~> Act (Unit :: m) x
  multiplicator :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act (a ** b) x ~> Act a (Act b x)
  multiplicatorInv :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act a (Act b x) ~> Act (a ** b) x

instance (CategoryOf k, Strong () ((~>) :: CAT k)) => MonoidalAction () k where
  type Act '() x = x
  withObAct r = r
  unitor = id
  unitorInv = id
  multiplicator = id
  multiplicatorInv = id

instance (Strong k p) => Strong (OPPOSITE k) (Op p) where
  act (Op w) (Op p) = Op (act w p)
instance (MonoidalAction m k) => MonoidalAction (OPPOSITE m) (OPPOSITE k) where
  type Act (OP a) (OP b) = OP (Act a b)
  withObAct @(OP a) @(OP b) r = withObAct @m @k @a @b r
  unitor = Op (unitorInv @m)
  unitorInv = Op (unitor @m)
  multiplicator @(OP a) @(OP b) @(OP x) = Op (multiplicatorInv @m @k @a @b @x)
  multiplicatorInv @(OP a) @(OP b) @(OP x) = Op (multiplicator @m @k @a @b @x)

instance (SubMonoidal ob) => Strong (SUBCAT (ob :: OB Type)) (->) where
  act (Sub f) g = f `par` g
instance (SubMonoidal ob) => Strong (SUBCAT (ob :: OB ())) U.Unit where
  act (Sub f) g = f `par` g

instance (Monoidal k, Monoidal (SUBCAT (ob :: OB k)), Strong (SUBCAT (ob :: OB k)) ((~>) :: CAT k)) => MonoidalAction (SUBCAT (ob :: OB k)) k where
  type Act (p :: SUBCAT ob) (x :: k) = UN SUB p ** x
  withObAct @(SUB a) @x r = withOb2 @k @a @x r
  unitor = leftUnitor @k
  unitorInv = leftUnitorInv @k
  multiplicator @(SUB p) @(SUB q) @x = associator @_ @p @q @x
  multiplicatorInv @(SUB p) @(SUB q) @x = associatorInv @_ @p @q @x

newtype Action a x y = Action (Rep (Action' a) x y)
deriving newtype instance (Ob (a :: m), MonoidalAction m k) => Profunctor (Action a :: k +-> k)
deriving newtype instance (Ob (a :: m), MonoidalAction m k) => Representable (Action a :: k +-> k)

data family Action' :: m -> k +-> k
instance (MonoidalAction m k, Ob a) => FunctorForRep (Action' (a :: m) :: k +-> k) where
  type Action' a @ x = Act a x
  fmap = act @m (obj @a)

par0Action :: (MonoidalAction m k, Ob (x :: k)) => Action (Unit :: m) x x
par0Action @m @k = Action (Rep (unitorInv @m @k))

parAction
  :: forall {m} {k} a b x y z
   . (MonoidalAction m k, Ob a, Ob b) => Action (a :: m) (x :: k) y -> Action (b :: m) y z -> Action (a ** b) x z
parAction (Action (Rep f)) (Action (Rep g)) = Action (Rep (composeActs @a @b @z f g))

class (MonoidalAction m k, SymMonoidal m) => SymMonoidalAction m k
instance (MonoidalAction m k, SymMonoidal m) => SymMonoidalAction m k

class (Act a b ~ a ** b) => ActIsTensor a b
instance (Act a b ~ a ** b) => ActIsTensor a b
class (Act a (Act b c) ~ a ** (b ** c), a ** (Act b c) ~ a ** (b ** c), Act a (b ** c) ~ a ** (b ** c)) => ActIsTensor3 a b c
instance (Act a (Act b c) ~ a ** (b ** c), a ** (Act b c) ~ a ** (b ** c), Act a (b ** c) ~ a ** (b ** c)) => ActIsTensor3 a b c
class
  ( SymMonoidalAction k k
  , Strong k ((~>) :: k +-> k)
  , forall (a :: k) (b :: k). ActIsTensor a b
  , forall (a :: k) (b :: k) (c :: k). ActIsTensor3 a b c
  ) =>
  SelfAction k
instance
  ( SymMonoidalAction k k
  , Strong k ((~>) :: k +-> k)
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
composeActs f g = multiplicatorInv @m @k @x @y @c . act (obj @x) g . f

decomposeActs
  :: forall {m} {k} (x :: m) y (c :: k) a b
   . (MonoidalAction m k, Ob x, Ob y, Ob c)
  => Act y c ~> b
  -> Act x b ~> a
  -> Act (x ** y) c ~> a
decomposeActs f g = g . act (obj @x) f . multiplicator @m @k @x @y @c

first' :: forall {k} {p :: CAT k} c a b. (SelfAction k, Strong k p, Ob c) => p a b -> p (a ** c) (b ** c)
first' p = dimap (swap @k @a @c) (swap @k @c @b) (second' @c p) \\ p

second' :: forall {k} {p :: CAT k} c a b. (SelfAction k, Strong k p, Ob c) => p a b -> p (c ** a) (c ** b)
second' p = act (obj @c) p

-- | If a strong profunctor is representable, we get the usual strength for the representing functor.
strength :: forall {m} p a b. (Representable p, Strong m p, Ob (a :: m), Ob b) => Act a (p % b) ~> p % Act a b
strength = index (act (obj @a) (trivialRep @p @b))

-- | If a strong profunctor is corepresentable, we get the usual costrength for the representing functor.
costrength :: forall {m} p a b. (Corepresentable p, Strong m p, Ob (a :: m), Ob b) => p %% Act a b ~> Act a (p %% b)
costrength = coindex (act (obj @a) (trivialCorep @p @b))

-- | This is not monoidal `par` but premonoidal, i.e. no sliding.
-- So with `prepar f g` the effects of f happen before the effects of g.
-- p needs to be a commutative promonad for this to be monoidal `par`.
prepar
  :: forall {k} {p :: CAT k} a b c d. (SelfAction k, Strong k p, Promonad p) => p a b -> p c d -> p (a ** c) (b ** d)
prepar f g = second' @b g . first' @c f \\ f \\ g

strongPar0 :: forall {k} {p :: CAT k} a. (SelfAction k, Strong k p, MonoidalProfunctor p, Ob a) => p a a
strongPar0 = dimap rightUnitorInv rightUnitor (act (obj @a) par0)

type Costrong :: forall {j} {k}. Kind -> j +-> k -> Constraint
class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Costrong m (p :: c +-> d) where
  coact :: forall (a :: m) (x :: d) (y :: c). (Ob a, Ob x, Ob y) => p (Act a x) (Act a y) -> p x y

trace :: forall {k} (p :: k +-> k) u x y. (SelfAction k, Costrong k p, Ob x, Ob y, Ob u) => p (x ** u) (y ** u) -> p x y
trace p = coact @k @p @u @x @y (dimap (swap @k @u @x) (swap @k @y @u) p) \\ p

class (SelfAction k, Costrong k ((~>) :: CAT k)) => TracedMonoidal k
instance (SelfAction k, Costrong k ((~>) :: CAT k)) => TracedMonoidal k
