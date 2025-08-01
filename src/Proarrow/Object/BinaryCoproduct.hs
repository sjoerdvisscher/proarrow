{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.BinaryCoproduct where

import Data.Kind (Type)
import Prelude (($), type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..), Costrong (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Object (Obj, obj, tgt)
import Proarrow.Object.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Coproduct (coproduct, (:+:) (..))
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Identity (Id (..))

infixl 4 ||
infixl 4 |||
infixl 4 +++

class (CategoryOf k) => HasBinaryCoproducts k where
  type (a :: k) || (b :: k) :: k
  withObCoprod :: (Ob (a :: k), Ob b) => ((Ob (a || b)) => r) -> r
  lft :: (Ob (a :: k), Ob b) => a ~> (a || b)
  rgt :: (Ob (a :: k), Ob b) => b ~> (a || b)
  (|||) :: (x :: k) ~> a -> y ~> a -> (x || y) ~> a
  (+++) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a || b ~> x || y
  l +++ r = (lft @k @x @y . l) ||| (rgt @k @x @y . r) \\ l \\ r

lft' :: forall {k} (a :: k) a' b. (HasBinaryCoproducts k) => a ~> a' -> Obj b -> a ~> (a' || b)
lft' a b = lft @k @a' @b . a \\ a \\ b

rgt' :: forall {k} (a :: k) b b'. (HasBinaryCoproducts k) => Obj a -> b ~> b' -> b ~> (a || b')
rgt' a b = rgt @k @a @b' . b \\ a \\ b

left :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryCoproducts k, Ob c) => a ~> b -> (a || c) ~> (b || c)
left f = f +++ obj @c

right :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryCoproducts k, Ob c) => a ~> b -> (c || a) ~> (c || b)
right f = obj @c +++ f

codiag :: forall {k} (a :: k). (HasBinaryCoproducts k, Ob a) => (a || a) ~> a
codiag = id ||| id

swapCoprod' :: (HasBinaryCoproducts k) => (a :: k) ~> a' -> b ~> b' -> (a || b) ~> (b' || a')
swapCoprod' a b = rgt' (tgt b) a ||| lft' b (tgt a)

swapCoprod :: (HasBinaryCoproducts k, Ob a, Ob b) => (a :: k) || b ~> b || a
swapCoprod @_ @a @b = swapCoprod' (obj @a) (obj @b)

type HasCoproducts k = (HasInitialObject k, HasBinaryCoproducts k)

class ((a ** b) ~ (a || b)) => TensorIsCoproduct a b
instance ((a ** b) ~ (a || b)) => TensorIsCoproduct a b
class
  (HasCoproducts k, Monoidal k, (Unit :: k) ~ InitialObject, forall (a :: k) (b :: k). TensorIsCoproduct a b) =>
  Cocartesian k
instance
  (HasCoproducts k, Monoidal k, (Unit :: k) ~ InitialObject, forall (a :: k) (b :: k). TensorIsCoproduct a b)
  => Cocartesian k

instance HasBinaryCoproducts Type where
  type a || b = P.Either a b
  withObCoprod r = r
  lft = P.Left
  rgt = P.Right
  (|||) = P.either

instance HasBinaryCoproducts () where
  type '() || '() = '()
  withObCoprod r = r
  lft = U.Unit
  rgt = U.Unit
  U.Unit ||| U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => HasBinaryCoproducts (j +-> k) where
  type p || q = p :+: q
  withObCoprod r = r
  lft = Prof InjL
  rgt = Prof InjR
  Prof l ||| Prof r = Prof (coproduct l r)

instance (HasBinaryCoproducts k) => HasBinaryCoproducts (PROD k) where
  type PR a || PR b = PR (a || b)
  withObCoprod @(PR a) @(PR b) r = withObCoprod @k @a @b r
  lft @(PR a) @(PR b) = Prod (lft @_ @a @b)
  rgt @(PR a) @(PR b) = Prod (rgt @_ @a @b)
  Prod l ||| Prod r = Prod (l ||| r)

newtype COPROD k = COPR k
type instance UN COPR (COPR k) = k

type Coprod :: j +-> k -> COPROD j +-> COPROD k
data Coprod p a b where
  Coprod :: {unCoprod :: p a b} -> Coprod p (COPR a) (COPR b)

instance (Profunctor p) => Profunctor (Coprod p) where
  dimap (Coprod (Id l)) (Coprod (Id r)) (Coprod p) = Coprod (dimap l r p)
  r \\ Coprod f = r \\ f
instance (Promonad p) => Promonad (Coprod p) where
  id = Coprod id
  Coprod f . Coprod g = Coprod (f . g)
-- | The same category as the category of @k@, but with coproducts as the tensor.
instance (CategoryOf k) => CategoryOf (COPROD k) where
  type (~>) = Coprod Id
  type Ob a = (Is COPR a, Ob (UN COPR a))

instance (HasCoproducts k) => MonoidalProfunctor (Coprod (Id :: k +-> k)) where
  par0 = Coprod id
  Coprod (Id f) `par` Coprod (Id g) = Coprod (Id (f +++ g))

instance (HasCoproducts j, HasCoproducts k) => MonoidalProfunctor (Coprod (TerminalProfunctor :: j +-> k)) where
  par0 = Coprod TerminalProfunctor
  Coprod (TerminalProfunctor @a1 @b1) `par` Coprod (TerminalProfunctor @a2 @b2) =
    withObCoprod @k @a1 @a2 $ withObCoprod @j @b1 @b2 $ Coprod TerminalProfunctor

copar0 :: (MonoidalProfunctor (Coprod p)) => p InitialObject InitialObject
copar0 = unCoprod par0

copar :: (MonoidalProfunctor (Coprod p)) => p a b -> p c d -> p (a || c) (b || d)
copar p q = unCoprod (Coprod p `par` Coprod q)

-- | Coproducts as monoidal tensor.
instance (HasCoproducts k) => Monoidal (COPROD k) where
  type Unit = COPR InitialObject
  type a ** b = COPR (UN COPR a || UN COPR b)
  withOb2 @(COPR a) @(COPR b) r = withObCoprod @k @a @b r
  leftUnitor = Coprod (Id (initiate ||| id))
  leftUnitorInv = Coprod (Id (rgt @_ @InitialObject))
  rightUnitor = Coprod (Id (id ||| initiate))
  rightUnitorInv = Coprod (Id (lft @_ @_ @InitialObject))
  associator @(COPR a) @(COPR b) @(COPR c) = Coprod (Id ((obj @a +++ lft @k @b @c) ||| (withObCoprod @k @b @c (rgt @k @a @(b || c)) . rgt @k @b @c)))
  associatorInv @(COPR a) @(COPR b) @(COPR c) = Coprod (Id ((withObCoprod @k @a @b (lft @k @(a || b) @c) . lft @k @a @b) ||| (rgt @k @a @b +++ obj @c)))

instance (HasCoproducts k) => SymMonoidal (COPROD k) where
  swap @(COPR a) @(COPR b) = Coprod (Id (swapCoprod @k @a @b))

instance Costrong (COPROD Type) (Coprod (Id :: CAT Type)) where
  coact (Coprod (Id uxuy)) = Coprod (Id (let loop ux = P.either (loop . P.Left) id (uxuy ux) in loop . P.Right))

instance HasCoproducts k => Strong (COPROD k) (Coprod (Id :: CAT k)) where
  act = par
instance HasCoproducts k => MonoidalAction (COPROD k) (COPROD k) where
  type Act p x = p ** x
  withObAct @(COPR a) @(COPR b) r = withObCoprod @k @a @b r
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator @(COPR a) @(COPR b) @(COPR c) = associatorInv @_ @(COPR a) @(COPR b) @(COPR c)
  multiplicatorInv @(COPR a) @(COPR b) @(COPR c) = associator @_ @(COPR a) @(COPR b) @(COPR c)

instance Strong Type (Coprod (Id :: CAT Type)) where
  l `act` Coprod (Id r) = Coprod (Id (l `par` r))
instance MonoidalAction Type (COPROD Type) where
  type Act p (COPR x) = COPR (p ** x)
  withObAct r = r
  unitor = Coprod (Id leftUnitor)
  unitorInv = Coprod (Id leftUnitorInv)
  multiplicator = Coprod (Id associatorInv)
  multiplicatorInv = Coprod (Id associator)

instance Strong (COPROD Type) (->) where
  Coprod (Id f) `act` g = f +++ g
instance MonoidalAction (COPROD Type) Type where
  type Act (p :: COPROD Type) (x :: Type) = UN COPR (p ** COPR x)
  withObAct r = r
  unitor = unId (unCoprod leftUnitor)
  unitorInv = unId (unCoprod leftUnitorInv)
  multiplicator = unId (unCoprod associatorInv)
  multiplicatorInv = unId (unCoprod associator)

class (Act (COPR a) b ~ (a || b)) => ActIsCoprod a b
instance (Act (COPR a) b ~ (a || b)) => ActIsCoprod a b
class (HasCoproducts k, forall (a :: k) (b :: k). ActIsCoprod a b, MonoidalAction (COPROD k) k) => CoprodAction k
instance (HasCoproducts k, forall (a :: k) (b :: k). ActIsCoprod a b, MonoidalAction (COPROD k) k) => CoprodAction k
class (Strong (COPROD k) p, CoprodAction k) => StrongCoprod (p :: CAT k)
instance (Strong (COPROD k) p, CoprodAction k) => StrongCoprod (p :: CAT k)

left' :: forall {k} (p :: CAT k) c a b. (StrongCoprod p, Ob c) => p a b -> p (a || c) (b || c)
left' p = dimap (swapCoprod @_ @a @c) (swapCoprod @_ @c @b) (right' @_ @c p) \\ p

right' :: forall {k} (p :: CAT k) c a b. (StrongCoprod p, Ob c) => p a b -> p (c || a) (c || b)
right' p = act (obj @(COPR c)) p
