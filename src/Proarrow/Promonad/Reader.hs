module Proarrow.Promonad.Reader where

import Prelude (($))

import Proarrow.Adjunction qualified as Adj
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , first
  , leftUnitorInvWith
  , leftUnitorWith
  , second
  , swap'
  , swapInner
  , unitObj
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..))
import Proarrow.Category.Monoidal.Distributive (Cotraversable (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, obj, rmap, src, (//), (:~>), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryProduct (Cartesian)
import Proarrow.Object.Exponential (Closed (..), uncurry)
import Proarrow.Profunctor.Composition (compComp, (:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Day (Day (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Profunctor.Star (Star, pattern Star)
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Promonad.Writer (Writer (..), WriterT (..))

data Reader r a b where
  Reader :: forall a b r. (Ob a) => r ** a ~> b -> Reader (OP r) a b

instance (Ob (r :: k), Monoidal k) => Profunctor (Reader (OP r) :: k +-> k) where
  dimap l r (Reader f) = Reader (r . f . second @r l) \\ r \\ l
  r \\ Reader f = r \\ f

-- | The coreader comonad given the Promonad instance.
-- Together with the 'Representable' instance this gives the curry/uncurry adjunction.
instance (Ob (r :: k), Monoidal k) => Corepresentable (Reader (OP r) :: k +-> k) where
  type Reader (OP r) %% a = r ** a
  coindex (Reader f) = f
  cotabulate = Reader
  corepMap = second @r

-- | The reader monad given the Promonad instance.
instance (Ob (r :: k), SymMonoidal k, Closed k) => Representable (Reader (OP r) :: k +-> k) where
  type Reader (OP r) % a = r ~~> a
  index (Reader @a @b f) = curry @_ @a @r @b (f . swap @_ @a @r)
  tabulate @b @a f = Reader (uncurry @r @b f . swap @_ @r @a) \\ f
  repMap f = f ^^^ obj @r

instance (Monoidal k) => Functor (Reader :: OPPOSITE k -> k +-> k) where
  map (Op f) = f // Prof \(Reader @a g) -> Reader (g . first @a f)

instance (Comonoid (r :: k), Monoidal k) => Promonad (Reader (OP r) :: k +-> k) where
  id = Reader (leftUnitorWith (counit @r))
  Reader g . Reader @a f = Reader (g . second @r f . associator @k @r @r @a . first @a (comult @r))

instance (Monoid (r :: k), Monoidal k) => Procomonad (Reader (OP r) :: k +-> k) where
  proextract (Reader f) = f . leftUnitorInvWith (mempty @r)
  produplicate (Reader @a f) = Reader id :.: Reader (f . first @a (mappend @r) . associatorInv @k @r @r @a) \\ f

instance (Ob (r :: k), SelfAction k) => Strong k (Reader (OP r) :: k +-> k) where
  act @a @_ @x @_ f (Reader g) =
    f //
      withObAct @k @k @a @x $
        Reader ((f `par` g) . associator @k @a @r @x . first @x (swap @_ @r @a) . associatorInv @k @r @a @x)

-- | Note: This is only premonoidal, not monoidal, unless the comonoid is cocommutative.
instance (Comonoid (r :: k), SelfAction k, SymMonoidal k) => MonoidalProfunctor (Reader (OP r) :: k +-> k) where
  par0 = id \\ unitObj @k
  Reader @x1 @x2 f `par` Reader @y1 @y2 g =
    f //
      g //
        withOb2 @_ @x1 @y1 $
          withOb2 @_ @x2 @y2 $
            Reader
              ( second @x2 g
                  . associator @k @x2 @r @y1
                  . ((swap' (obj @r) f . associator @k @r @r @x1 . first @x1 (comult @r)) `par` obj @y1)
                  . associatorInv @k @r @x1 @y1
              )

-- | A version of cotraverse specialized to `Reader`, with fewer requirements on @p@.
cotraverseReader
  :: forall {k} p (r :: k). (Strong k p, SelfAction k, Ob r) => p :.: Reader (OP r) :~> Reader (OP r) :.: p
cotraverseReader (p :.: Reader f) = let rp = obj @r `act` p in Reader (src rp) :.: rmap f rp \\ rp \\ p

instance (Comonoid (r :: k), SelfAction k) => Cotraversable (Reader (OP r) :: k +-> k) where
  cotraverse = cotraverseReader

-- Reader is not Traversable

instance (Ob (r :: k), Monoidal k) => Adj.Proadjunction (Writer r :: k +-> k) (Reader (OP r)) where
  unit @a = withOb2 @k @r @a $ Reader id :.: Writer id
  counit (Writer f :.: Reader g) = g . f

dayCounit :: forall {k} (r :: k). (Ob r, Cartesian k) => Writer r `Day` Reader (OP r) ~> (~>)
dayCounit = Prof \(Day @_ @d @e f (Writer p) (Reader q) g) -> g . second @d q . associator @k @d @r @e . first @e (swap @k @r @d . p) . f

readerComp
  :: forall {k} (r :: k) (s :: k). (SymMonoidal k, Ob r, Ob s) => Reader (OP r) :.: Reader (OP s) ~> Reader (OP (r ** s))
readerComp = withOb2 @k @r @s $
  Prof \(Reader @a f :.: Reader g) -> Reader (g . second @s f . associator @k @s @r @a . first @a (swap @k @r @s))

readerDay
  :: forall {k} (r :: k) (s :: k). (SymMonoidal k, Ob r, Ob s) => Reader (OP r) `Day` Reader (OP s) ~> Reader (OP (r ** s))
readerDay = withOb2 @k @r @s $
  Prof \(Day @c @_ @e @_ f (Reader p) (Reader q) g) -> Reader (g . (p `par` q) . swapInner @r @s @c @e . second @(r ** s) f) \\ f

type ReaderT :: OPPOSITE k -> k +-> k -> k +-> k
newtype ReaderT r p a b where
  ReaderT :: (Reader r :.: p) a b -> ReaderT r p a b

runReaderT :: (Profunctor p) => ReaderT (OP r) p a b -> p (r ** a) b
runReaderT (ReaderT (Reader f :.: p)) = lmap f p

ask :: (Promonad p, Monoidal k, Ob (r :: k)) => ReaderT (OP r) p Unit r
ask = ReaderT (Reader rightUnitor :.: id)

answer
  :: forall {k} p r a b. (Promonad p, Monoidal k, Comonoid (r :: k)) => ReaderT (OP r) p a b -> ReaderT (OP r) p (r ** a) b
answer (ReaderT (Reader f :.: p)) = withOb2 @k @r @a $ ReaderT (Reader (f . leftUnitorWith @(r ** a) (counit @r)) :.: p)

local :: forall {k} a b p r. (Monoidal k, Ob (r :: k)) => r ~> r -> ReaderT (OP r) p a b -> ReaderT (OP r) p a b
local f (ReaderT (Reader r :.: p)) = ReaderT (Reader (r . first @a f) :.: p)

deriving newtype instance (Profunctor p, Monoidal k, Ob (r :: k)) => Profunctor (ReaderT (OP r) p)
deriving newtype instance (Representable p, Ob (r :: k), SymMonoidal k, Closed k) => Representable (ReaderT (OP r) p)
deriving newtype instance (Corepresentable p, Ob (r :: k), Monoidal k) => Corepresentable (ReaderT (OP r) p)
deriving newtype instance (Strong k p, Ob (r :: k), SelfAction k) => Strong k (ReaderT (OP r) p)
deriving newtype instance
  (MonoidalProfunctor p, Comonoid (r :: k), SelfAction k, SymMonoidal k) => MonoidalProfunctor (ReaderT (OP r) p)
deriving newtype instance (Cotraversable p, Comonoid (r :: k), SelfAction k) => Cotraversable (ReaderT (OP r) p)

instance (Monoidal k, Ob r) => Functor (ReaderT r :: k +-> k -> k +-> k) where
  map n@Prof{} = Prof \(ReaderT p) -> ReaderT (unProf (map n) p)

instance (Monoidal k) => Functor (ReaderT :: OPPOSITE k -> k +-> k -> k +-> k) where
  map f = f // Nat $ Prof \(ReaderT p) -> ReaderT (unProf (unNat (map (map f))) p)

instance (Comonoid (r :: k), SelfAction k, Strong k p, Promonad p) => Promonad (ReaderT (OP r) p) where
  id = ReaderT (id :.: id)
  ReaderT l . ReaderT r = ReaderT (compComp cotraverseReader l r)

-- | ReaderT is a monad on profunctors, i.e. we have @p ~> ReaderT p@ and @ReaderT (ReaderT p) ~> ReaderT p@.
instance (Comonoid r, Monoidal k) => Promonad (Star (ReaderT (OP r) :: k +-> k -> k +-> k)) where
  id = Star $ Prof \p -> ReaderT (id :.: p) \\ p
  Star l . Star r = Star $ Prof (\(ReaderT (f :.: ReaderT (g :.: p))) -> ReaderT ((g . f) :.: p)) . map l . r

instance (Adj.Proadjunction p q, Ob (r :: k), Monoidal k) => Adj.Proadjunction (WriterT r p) (ReaderT (OP r) q) where
  unit @a = case Adj.unit @_ @_ @a of l :.: r -> ReaderT l :.: WriterT r
  counit (WriterT l :.: ReaderT r) = Adj.counit (l :.: r)
