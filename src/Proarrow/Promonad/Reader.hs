module Proarrow.Promonad.Reader where

import Prelude (($))

import Proarrow.Adjunction qualified as Adj
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
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..), strongPar0)
import Proarrow.Category.Monoidal.Distributive (Cotraversable (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, rmap, src, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryProduct (Cartesian)
import Proarrow.Object.Exponential (Closed (..), uncurry)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Day (Day (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Promonad.Writer (Writer (..))

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
  cotabulate f = Reader f
  corepMap f = second @r f

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
  extract (Reader f) = f . leftUnitorInvWith (mempty @r)
  duplicate (Reader @a f) = Reader id :.: Reader (f . first @a (mappend @r) . associatorInv @k @r @r @a) \\ f

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

instance (Comonoid (r :: k), SelfAction k) => Cotraversable (Reader (OP r) :: k +-> k) where
  cotraverse (p :.: Reader f) = let rp = unId (strongPar0 @r) `act` p in Reader (src rp) :.: rmap f rp \\ rp \\ p

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