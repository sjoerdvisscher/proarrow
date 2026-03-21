{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Proarrow.Category.Equipment.Stateful where

import Prelude (type (~))

import Proarrow.Adjunction (Proadjunction)
import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..), Adjunction_ (..), Adj (..))
import Proarrow.Category.Bicategory.Prof (PROFK (..), Prof (..))
import Proarrow.Category.Equipment (Cotight, CotightAdjoint, Equipment (..), IsOb, Tight, TightAdjoint, WithObO2 (..))
import Proarrow.Category.Monoidal.Action (Strong (..), SelfAction, actHom)
import Proarrow.Category.Opposite (OPPOSITE (..))
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
  , rmap
  , src
  , tgt
  , (:~>)
  , type (+->), obj
  )
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Promonad.Reader (Reader (..))
import Proarrow.Promonad.Writer (Writer (..))
import Proarrow.Profunctor.Product ((:*:)(..))
import Proarrow.Profunctor.Coproduct ((:+:) (..))

type STT' :: Kind -> CAT ()
newtype STT' k i j = ST (k +-> k)
type instance UN ST (ST p) = p
type STT k = STT' k '() '()

type StT :: CAT (STT' k i j)
data StT a b where
  StT :: (Strong k p, Strong k q) => p :~> q -> StT (ST p :: STT' k i j) (ST q)
instance (SelfAction k) => Profunctor (StT :: CAT (STT' k i j)) where
  dimap = dimapDefault
  r \\ StT p = r \\ p
instance (SelfAction k) => Promonad (StT :: CAT (STT' k i j)) where
  id = StT id
  StT f . StT g = StT (f . g)
instance (SelfAction k) => CategoryOf (STT' k i j) where
  type (~>) = StT
  type Ob (a :: STT' k i j) = (Is ST a, Strong k (UN ST a))

instance (SelfAction k) => Bicategory (STT' k) where
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
  (SelfAction k, Adjunction (PK l) (PK r), Ob l, Ob r, Strong k r, Strong k l)
  => Adjunction_ (ST l :: STT' k i j) (ST r)
  where
    adj = Adj
      { adjUnit = StT (case unit @(PK l) @(PK r) of Prof f -> f)
      , adjCounit = StT (case counit @(PK l) @(PK r) of Prof f -> f)
      }

class
  ( IsReader (WithReader p)
  , Strong k (WithReader p)
  , Proadjunction p (WithReader p)
  , WithWriter (WithReader p) ~ p
  ) =>
  IsWriter (p :: k +-> k)
  where
  type WithReader p :: k +-> k
instance (SelfAction k) => IsWriter (Id :: k +-> k) where type WithReader Id = Id
instance (SelfAction k, Ob (a :: k)) => IsWriter (Writer a :: k +-> k) where
  type WithReader (Writer a) = Reader (OP a)
instance (IsWriter p, IsWriter q) => IsWriter (p :.: q) where
  type WithReader (p :.: q) = WithReader q :.: WithReader p

class
  ( IsWriter (WithWriter p)
  , Strong k (WithWriter p)
  , Proadjunction (WithWriter p) p
  , WithReader (WithWriter p) ~ p
  ) =>
  IsReader (p :: k +-> k)
  where
  type WithWriter p :: k +-> k
instance (SelfAction k) => IsReader (Id :: k +-> k) where type WithWriter Id = Id
instance (SelfAction k, Ob (a :: k)) => IsReader (Reader (OP a) :: k +-> k) where
  type WithWriter (Reader (OP a)) = Writer a
instance (IsReader p, IsReader q) => IsReader (p :.: q) where
  type WithWriter (p :.: q) = WithWriter q :.: WithWriter p

type instance IsOb Tight (p :: STT' k i j) = IsWriter (UN ST p)
type instance IsOb Cotight (p :: STT' k i j) = (IsReader (UN ST p))
type instance CotightAdjoint (p :: STT' k i j) = ST (WithReader (UN ST p))
type instance TightAdjoint (p :: STT' k i j) = ST (WithWriter (UN ST p))
instance (SelfAction k) => WithObO2 Tight (STT' k) where withObO2 r = r
instance (SelfAction k) => WithObO2 Cotight (STT' k) where withObO2 r = r

-- | Stateful transformers.
-- https://arxiv.org/pdf/2305.16899 definition 6
-- Generalized to any symmetric monoidal action.
instance (SelfAction k) => Equipment (STT' k) where
  withTightAdjoint r = r
  withCotightAdjoint r = r

type STSq (p :: k +-> k) (q :: k +-> k) (a :: k) (b :: k) = ST (Writer a) `O` (ST p :: STT k) ~> (ST q :: STT k) `O` ST (Writer a)

crossing
  :: forall {k} (p :: k +-> k) (a :: k)
   . (Strong k p, Ob a, SelfAction k) => STSq p p a a
crossing = StT \(Writer g :.: p) -> lmap g (act (obj @a) p) :.: Writer (obj @a `actHom` tgt p) \\ p

pi0
  :: forall {k} (p :: STT k) (q :: STT k). (Ob p, Ob q, SelfAction k) => ST (UN ST p :*: UN ST q) ~> p
pi0 = StT \(p :*: _) -> p

pi1
  :: forall {k} (p :: STT k) (q :: STT k). (Ob p, Ob q, SelfAction k) => ST (UN ST p :*: UN ST q) ~> q
pi1 = StT \(_ :*: q) -> q

mult
  :: forall {k} (p :: STT k) q r (a :: k) b
   . (Ob p, Ob q, Ob r, SelfAction k, Ob a, Ob b)
  => p ~> q -> p ~> r -> p ~> ST (UN ST q :*: UN ST r)
StT n `mult` StT m = StT \p -> n p :*: m p

ip0
  :: forall {k} (p :: STT k) q. (Ob p, Ob q, SelfAction k) => p ~> ST (UN ST p :+: UN ST q)
ip0 = StT \p -> InjL p

ip1
  :: forall {k} (p :: STT k) q. (Ob p, Ob q, SelfAction k) => q ~> ST (UN ST p :+: UN ST q)
ip1 = StT \p -> InjR p

-- plus
--   :: forall {k} (p :: k +-> k) q r (a :: k) b
--    . (Strong k p, Strong k q, Strong k r, M.SymMonoidal m, Ob a, Ob b)
--   => STSq p r a b -> STSq q r a b -> STSq (p :+: q) r a b
-- STSq n `plus` STSq m = STSq (coproduct n m)

-- sigma0
--   :: forall {k} (a :: k) b
--    . (Ob a, Ob b, M.SymMonoidal m, SelfAction k, HasCoproducts m) => STSq (Id :: k +-> k) Id a (a || b)
-- sigma0 = withObCoprod @m @a @b $ STSq \(Id f) -> Id (act (lft @m @a @b) f)

-- sigma1
--   :: forall {k} (a :: k) b
--    . (Ob a, Ob b, M.SymMonoidal m, SelfAction k, HasCoproducts m) => STSq (Id :: k +-> k) Id b (a || b)
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
