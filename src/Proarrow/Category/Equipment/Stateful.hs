{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Proarrow.Category.Equipment.Stateful where

import Prelude (($))

import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Category.Bicategory.Prof (PROFK (..), Prof (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..))
import Proarrow.Category.Instance.Prof (unProf)
import Proarrow.Category.Monoidal (MonoidalProfunctor, par)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..), toSelfAct)
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

type STT :: Kind -> Kind -> CAT ()
newtype STT m k i j = ST (k +-> k)
type instance UN ST (ST p) = p

type StT :: CAT (STT m k i j)
data StT a b where
  StT :: (Strong m p, Strong m q) => p :~> q -> StT (ST p :: STT m k i j) (ST q)
instance (MonoidalAction m k) => Profunctor (StT :: CAT (STT m k i j)) where
  dimap = dimapDefault
  r \\ StT p = r \\ p
instance (MonoidalAction m k) => Promonad (StT :: CAT (STT m k i j)) where
  id = StT id
  StT f . StT g = StT (f . g)
instance (MonoidalAction m k) => CategoryOf (STT m k i j) where
  type (~>) = StT
  type Ob (a :: STT m k i j) = (Is ST a, Strong m (UN ST a))

instance (MonoidalAction m k) => Bicategory (STT m k) where
  type I = ST Id
  type ST a `O` ST b = ST (a :.: b)
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

-- | Stateful transformers.
-- https://arxiv.org/pdf/2305.16899 definition 6
-- Generalized to any monoidal action.
instance (MonoidalAction m k, M.SymMonoidal m) => HasCompanions (STT m k) (MonK m) where
  type Companion (STT m k) (MK a) = ST (Writer a)
  mapCompanion (Mon2 f) = StT (unProf (map f)) \\ f
  withObCompanion r = r
  compToId = StT \(Writer f) -> Id (unitor @m . f)
  compFromId = StT \(Id f) -> Writer (unitorInv @m . f) \\ f
  compToCompose (Mon2 @m1 m1) (Mon2 @m2 m2) =
    m1 // m2 // m1 `par` m2 // StT \(Writer @b f) ->
      let m2b = m2 `act` obj @b in Writer (multiplicatorInv @m @k @m1 @m2 @b . f) :.: Writer m2b \\ m2b
  compFromCompose (Mon2 m1) (Mon2 m2) =
    m1 // m2 // m1 `par` m2 // StT \(Writer @_ @_ @m1 f :.: Writer @c @_ @m2 g) ->
      Writer (multiplicator @m @k @m1 @m2 @c . act m1 g . f)

instance
  (MonoidalAction m k, M.SymMonoidal m, Adjunction (PK l) (PK r), Ob l, Ob r, Strong m r, Strong m l)
  => Adjunction (ST l :: STT m k i j) (ST r)
  where
  unit = StT (case unit @(PK l) @(PK r) of Prof f -> f)
  counit = StT (case counit @(PK l) @(PK r) of Prof f -> f)

instance (MonoidalAction m k, M.SymMonoidal m) => Equipment (STT m k) (MonK m) where
  type Conjoint (STT m k) (MK a) = ST (Reader (OP a))
  mapConjoint (Mon2 f) = StT (unProf (map (Op f))) \\ f
  withObConjoint r = r

type STSq (p :: k +-> k) (q :: k +-> k) (a :: m) (b :: m) =
  Sq '(ST p :: STT m k '() '(), MK a :: MonK m '() '()) '(ST q, MK b :: MonK m '() '())

unSTSq
  :: forall {m} {k} p q (a :: m) b
   . (M.SymMonoidal m)
  => STSq p q a b
  -> (forall x y. p x y -> q (Act a x) (Act b y), Obj a, Obj b, Obj (ST p :: STT m k '() '()), Obj (ST q :: STT m k '() '()))
unSTSq (Sq (StT f)) = (\p -> p // case f (Writer (obj @a `act` src p) :.: p) of q :.: Writer g -> rmap g q, Obj, Obj, Obj, Obj)

pattern STSq
  :: forall {m} {k} (p :: k +-> k) q (a :: m) b
   . (M.SymMonoidal m, MonoidalAction m k)
  => (Strong m p, Strong m q, Ob a, Ob b)
  => (forall x y. p x y -> q (Act a x) (Act b y)) -> STSq p q a b
pattern STSq f <- (unSTSq -> (f, Obj, Obj, Obj, Obj))
  where
    STSq f = Sq (StT (\(Writer g :.: p) -> lmap g (f p) :.: Writer (obj @b `act` tgt p) \\ p))

{-# COMPLETE STSq #-}

crossing
  :: forall {k} {m} p a. (Strong m (p :: k +-> k), Ob (a :: m), M.SymMonoidal m) => STSq p p a a
crossing = STSq (act (obj @a))

pi0
  :: forall {m} {k} p q. (Strong m (p :: k +-> k), Strong m q, M.SymMonoidal m) => STSq (p :*: q) p (M.Unit :: m) M.Unit
pi0 = STSq \(p :*: _) -> act (obj @(M.Unit :: m)) p

pi1
  :: forall {m} {k} p q. (Strong m (p :: k +-> k), Strong m q, M.SymMonoidal m) => STSq (p :*: q) q (M.Unit :: m) M.Unit
pi1 = STSq \(_ :*: q) -> act (obj @(M.Unit :: m)) q

mult
  :: forall {m} {k} (p :: k +-> k) q r (a :: m) b
   . (Strong m p, Strong m q, Strong m r, M.SymMonoidal m, Ob a, Ob b)
  => STSq p q a b -> STSq p r a b -> STSq p (q :*: r) a b
STSq n `mult` STSq m = STSq (\p -> n p :*: m p)

ip0
  :: forall {m} {k} p q. (Strong m (p :: k +-> k), Strong m q, M.SymMonoidal m) => STSq p (p :+: q) (M.Unit :: m) M.Unit
ip0 = STSq \p -> act (obj @(M.Unit :: m)) (InjL p)

ip1
  :: forall {m} {k} p q. (Strong m (p :: k +-> k), Strong m q, M.SymMonoidal m) => STSq q (p :+: q) (M.Unit :: m) M.Unit
ip1 = STSq \p -> act (obj @(M.Unit :: m)) (InjR p)

plus
  :: forall {m} {k} (p :: k +-> k) q r (a :: m) b
   . (Strong m p, Strong m q, Strong m r, M.SymMonoidal m, Ob a, Ob b)
  => STSq p r a b -> STSq q r a b -> STSq (p :+: q) r a b
STSq n `plus` STSq m = STSq (coproduct n m)

sigma0
  :: forall {m} {k} (a :: m) b
   . (Ob a, Ob b, M.SymMonoidal m, MonoidalAction m k, HasCoproducts m) => STSq (Id :: k +-> k) Id a (a || b)
sigma0 = withObCoprod @m @a @b $ STSq \(Id f) -> Id (act (lft @m @a @b) f)

sigma1
  :: forall {m} {k} (a :: m) b
   . (Ob a, Ob b, M.SymMonoidal m, MonoidalAction m k, HasCoproducts m) => STSq (Id :: k +-> k) Id b (a || b)
sigma1 = withObCoprod @m @a @b $ STSq \(Id f) -> Id (act (rgt @m @a @b) f)

copair
  :: forall {k} (p :: k +-> k) q (a :: k) b c
   . (Strong k p, Strong k q, M.SymMonoidal k, Distributive k, SelfAction k, MonoidalProfunctor (Coprod q), Ob a, Ob b, Ob c)
  => STSq p q a c -> STSq p q b c -> STSq p q (a || b) c
STSq n `copair` STSq m =
  withObCoprod @k @a @b $
    STSq
      ( \(p :: p x y) ->
          dimap ((toSelfAct @a @x +++ toSelfAct @b @x) . distR @k @a @b @x) (withObAct @k @k @c @y codiag) ((n p `copar` m p))
            \\ p
      )
