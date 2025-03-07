module Proarrow.Category.Equipment.Stateful where

import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Category.Bicategory.Prof (PROFK (..), Prof (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..))
import Proarrow.Category.Instance.Prof (unProf)
import Proarrow.Category.Monoidal (par)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
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
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Promonad.Reader (Reader)
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
instance (MonoidalAction m k, M.SymMonoidal m, Ob (M.Unit @m)) => HasCompanions (STT m k) (MonK m) where
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

instance (MonoidalAction m k, M.SymMonoidal m, Ob (M.Unit @m)) => Equipment (STT m k) (MonK m) where
  type Conjoint (STT m k) (MK a) = ST (Reader (OP a))
  mapConjoint (Mon2 f) = StT (unProf (map (Op f))) \\ f
  withObConjoint r = r

type STSq (p :: k +-> k) (q :: k +-> k) (a :: m) (b :: m) =
  Sq '(ST p :: STT m k '() '(), MK a :: MonK m '() '()) '(ST q, MK b :: MonK m '() '())

crossing
  :: forall {k} {m} p a. (Strong m (p :: k +-> k), Ob (a :: m), MonoidalAction m k, M.SymMonoidal m) => STSq p p a a
crossing =
  Sq
    ( StT \(Writer @_ @_ @w f :.: p) ->
        lmap f ((act (obj @a) p)) :.: Writer id
          \\ f
          \\ p
          \\ obj @w `act` tgt p
    )