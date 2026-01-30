{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Proarrow.Category.Equipment.Stateful where

import Prelude (($), type (~))

import Proarrow.Adjunction (Proadjunction)
import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Category.Bicategory.Prof (PROFK (..), Prof (..))
import Proarrow.Category.Equipment (Cotight, CotightAdjoint, Equipment (..), IsOb, Tight, TightAdjoint, WithObO2 (..))
import Proarrow.Category.Instance.Prof (unProf)
import Proarrow.Category.Monoidal (MonoidalProfunctor, par)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..), SymMonoidalAction, toSelfAct)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Is
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , UN
  , dimapDefault
  , lmap
  , obj
  , rmap
  , src
  , tgt
  , (//)
  , (:~>)
  , type (+->)
  )
import Proarrow.Functor (map)
import Proarrow.Object (pattern Obj, type Obj)
import Proarrow.Object.BinaryCoproduct (Coprod, HasBinaryCoproducts (..), HasCoproducts, codiag, copar)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Coproduct (coproduct, (:+:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Product ((:*:) (..))
import Proarrow.Promonad.Reader (Reader (..))
import Proarrow.Promonad.Writer (Writer (..))

type STT' :: Kind -> Kind -> CAT ()
newtype STT' m k i j = ST (k +-> k)
type instance UN ST (ST p) = p
type STT m k = STT' m k '() '()

type StT :: CAT (STT' m k i j)
data StT a b where
  StT :: (Strong m p, Strong m q) => p :~> q -> StT (ST p :: STT' m k i j) (ST q)
instance (MonoidalAction m k) => Profunctor (StT :: CAT (STT' m k i j)) where
  dimap = dimapDefault
  r \\ StT p = r \\ p
instance (MonoidalAction m k) => Promonad (StT :: CAT (STT' m k i j)) where
  id = StT id
  StT f . StT g = StT (f . g)
instance (MonoidalAction m k) => CategoryOf (STT' m k i j) where
  type (~>) = StT
  type Ob (a :: STT' m k i j) = (Is ST a, Strong m (UN ST a))

instance (MonoidalAction m k) => Bicategory (STT' m k) where
  type I = ST Id
  type a `O` b = ST (UN ST a :.: UN ST b)
  withOb2 r = r
  withOb0s r = r
  StT m `o` StT n = StT \(p :.: q) -> m p :.: n q
  r \\\ StT{} = r
  leftUnitor = StT \(Id h :.: q) -> lmap h q
  leftUnitorInv = StT \p -> Id (src p) :.: p
  rightUnitor = StT \(p :.: Id h) -> rmap h p
  rightUnitorInv = StT \p -> p :.: Id (tgt p)
  associator = StT \((p :.: q) :.: r) -> p :.: (q :.: r)
  associatorInv = StT \(p :.: (q :.: r)) -> (p :.: q) :.: r

instance
  (MonoidalAction m k, Adjunction (PK l) (PK r), Ob l, Ob r, Strong m r, Strong m l)
  => Adjunction (ST l :: STT' m k i j) (ST r)
  where
  unit = StT (case unit @(PK l) @(PK r) of Prof f -> f)
  counit = StT (case counit @(PK l) @(PK r) of Prof f -> f)

class
  ( IsReader m (WithReader m p)
  , Strong m (WithReader m p)
  , Proadjunction p (WithReader m p)
  , WithWriter m (WithReader m p) ~ p
  ) =>
  IsWriter m (p :: k +-> k)
  where
  type WithReader m p :: k +-> k
instance (SymMonoidalAction m k) => IsWriter m (Id :: k +-> k) where type WithReader m Id = Id
instance (SymMonoidalAction m k, Ob (a :: m)) => IsWriter m (Writer a :: k +-> k) where
  type WithReader m (Writer a) = Reader (OP a)
instance (IsWriter m p, IsWriter m q) => IsWriter m (p :.: q) where
  type WithReader m (p :.: q) = WithReader m q :.: WithReader m p

class
  ( IsWriter m (WithWriter m p)
  , Strong m (WithWriter m p)
  , Proadjunction (WithWriter m p) p
  , WithReader m (WithWriter m p) ~ p
  ) =>
  IsReader m (p :: k +-> k)
  where
  type WithWriter m p :: k +-> k
instance (SymMonoidalAction m k) => IsReader m (Id :: k +-> k) where type WithWriter m Id = Id
instance (SymMonoidalAction m k, Ob (a :: m)) => IsReader m (Reader (OP a) :: k +-> k) where
  type WithWriter m (Reader (OP a)) = Writer a
instance (IsReader m p, IsReader m q) => IsReader m (p :.: q) where
  type WithWriter m (p :.: q) = WithWriter m q :.: WithWriter m p

type instance IsOb Tight (p :: STT' m k i j) = IsWriter m (UN ST p)
type instance IsOb Cotight (p :: STT' m k i j) = (IsReader m (UN ST p))
type instance CotightAdjoint (p :: STT' m k i j) = ST (WithReader m (UN ST p))
type instance TightAdjoint (p :: STT' m k i j) = ST (WithWriter m (UN ST p))
instance (MonoidalAction m k) => WithObO2 Tight (STT' m k) where withObO2 r = r
instance (MonoidalAction m k) => WithObO2 Cotight (STT' m k) where withObO2 r = r

-- | Stateful transformers.
-- https://arxiv.org/pdf/2305.16899 definition 6
-- Generalized to any symmetric monoidal action.
instance (SymMonoidalAction m k) => Equipment (STT' m k) where
  withTightAdjoint r = r
  withCotightAdjoint r = r

type STSq (p :: k +-> k) (q :: k +-> k) (a :: m) (b :: m) = ST (Writer a) `O` (ST p :: STT m k) ~> (ST q :: STT m k) `O` ST (Writer a)

crossing
  :: forall {k} {m} (p :: k +-> k) (a :: m)
   . (Strong m p, Ob a, SymMonoidalAction m k) => STSq p p a a
crossing = StT \(Writer g :.: p) -> lmap g (act (obj @a) p) :.: Writer (obj @a `act` tgt p) \\ p

pi0
  :: forall {m} {k} (p :: STT m k) (q :: STT m k). (Ob p, Ob q, SymMonoidalAction m k) => ST (UN ST p :*: UN ST q) ~> p
pi0 = StT \(p :*: _) -> p

pi1
  :: forall {m} {k} (p :: STT m k) (q :: STT m k). (Ob p, Ob q, SymMonoidalAction m k) => ST (UN ST p :*: UN ST q) ~> q
pi1 = StT \(_ :*: q) -> q

-- mult
--   :: forall {m} {k} (p :: k +-> k) q r (a :: m) b
--    . (Strong m p, Strong m q, Strong m r, M.SymMonoidal m, Ob a, Ob b)
--   => STSq p q a b -> STSq p r a b -> STSq p (q :*: r) a b
-- STSq n `mult` STSq m = STSq (\p -> n p :*: m p)

-- ip0
--   :: forall {m} {k} p q. (Strong m (p :: k +-> k), Strong m q, M.SymMonoidal m) => STSq p (p :+: q) (M.Unit :: m) M.Unit
-- ip0 = STSq \p -> act (obj @(M.Unit :: m)) (InjL p)

-- ip1
--   :: forall {m} {k} p q. (Strong m (p :: k +-> k), Strong m q, M.SymMonoidal m) => STSq q (p :+: q) (M.Unit :: m) M.Unit
-- ip1 = STSq \p -> act (obj @(M.Unit :: m)) (InjR p)

-- plus
--   :: forall {m} {k} (p :: k +-> k) q r (a :: m) b
--    . (Strong m p, Strong m q, Strong m r, M.SymMonoidal m, Ob a, Ob b)
--   => STSq p r a b -> STSq q r a b -> STSq (p :+: q) r a b
-- STSq n `plus` STSq m = STSq (coproduct n m)

-- sigma0
--   :: forall {m} {k} (a :: m) b
--    . (Ob a, Ob b, M.SymMonoidal m, MonoidalAction m k, HasCoproducts m) => STSq (Id :: k +-> k) Id a (a || b)
-- sigma0 = withObCoprod @m @a @b $ STSq \(Id f) -> Id (act (lft @m @a @b) f)

-- sigma1
--   :: forall {m} {k} (a :: m) b
--    . (Ob a, Ob b, M.SymMonoidal m, MonoidalAction m k, HasCoproducts m) => STSq (Id :: k +-> k) Id b (a || b)
-- sigma1 = withObCoprod @m @a @b $ STSq \(Id f) -> Id (act (rgt @m @a @b) f)

-- copair
--   :: forall {k} (p :: k +-> k) q (a :: k) b c
--    . (Strong k p, Strong k q, M.SymMonoidal k, Distributive k, SelfAction k, MonoidalProfunctor (Coprod q), Ob a, Ob b, Ob c)
--   => STSq p q a c -> STSq p q b c -> STSq p q (a || b) c
-- STSq n `copair` STSq m =
--   withObCoprod @k @a @b $
--     STSq
--       ( \(p :: p x y) ->
--           dimap ((toSelfAct @a @x +++ toSelfAct @b @x) . distR @k @a @b @x) (withObAct @k @k @c @y codiag) ((n p `copar` m p))
--             \\ p
--       )
