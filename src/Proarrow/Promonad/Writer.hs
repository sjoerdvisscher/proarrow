{-# LANGUAGE TupleSections #-}

module Proarrow.Promonad.Writer where

import Prelude (($))

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
import Proarrow.Category.Monoidal.Distributive (Traversable (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, obj, rmap, tgt, (//), (:~>), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.Dual
  ( CompactClosed (..)
  , ExpSA
  , StarAutonomous (..)
  , combineDual
  , doubleNeg
  , doubleNegInv
  , dualityCounit
  , dualityUnit
  , expSA
  )
import Proarrow.Profunctor.Composition (compComp, (:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Day (Day (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)
import Proarrow.Profunctor.Star (Star, pattern Star)
import Proarrow.Promonad (Procomonad (..))

data Writer w a b where
  Writer :: (Ob b) => a ~> w ** b -> Writer w a b

instance (Ob (w :: k), Monoidal k) => Profunctor (Writer w :: k +-> k) where
  dimap = dimapRep
  r \\ Writer f = r \\ f

-- | The writer monad given the Promonad instance.
instance (Ob (w :: k), Monoidal k) => Representable (Writer w :: k +-> k) where
  type Writer w % a = w ** a
  index (Writer f) = f
  tabulate f = Writer f
  repMap f = obj @w `par` f

-- | The cowriter comonad given the Promonad instance.
instance (Ob (w :: k), SelfAction k, CompactClosed k) => Corepresentable (Writer w :: k +-> k) where
  type Writer w %% a = ExpSA w a
  coindex (Writer @b @a f) =
    leftUnitorWith (dualityCounit @w)
      . associatorInv @k @(Dual w) @w @b
      . (obj @(Dual w) `par` (f . doubleNeg @a))
      . distribDual @k @w @(Dual a)
      \\ f
  cotabulate @a f =
    Writer
      ( (obj @w `par` (f . combineDual @w @(Dual a)))
          . associator @k @w @(Dual w) @(Dual (Dual a))
          . leftUnitorInvWith (dualityUnit @w)
          . doubleNegInv @a
      )
      \\ f
  corepMap f = expSA f (obj @w)

instance (Monoidal k) => Functor (Writer :: k -> k +-> k) where
  map f = f // Prof \(Writer @b g) -> Writer ((f `par` obj @b) . g)

instance (Monoid (w :: k), Monoidal k) => Promonad (Writer w :: k +-> k) where
  id = Writer (leftUnitorInvWith (mempty @w))
  Writer @c g . Writer f = Writer (first @c (mappend @w) . associatorInv @k @w @w @c . second @w g . f)

instance (Comonoid (w :: k), Monoidal k) => Procomonad (Writer w :: k +-> k) where
  extract (Writer f) = leftUnitorWith (counit @w) . f
  duplicate (Writer @b f) = Writer (associator @k @w @w @b . first @b (comult @w) . f) :.: Writer id \\ f

instance (Ob (w :: k), SelfAction k) => Strong k (Writer w :: k +-> k) where
  act @_ @b @_ @y f (Writer g) =
    f //
      withObAct @k @k @b @y $
        Writer (associator @k @w @b @y . first @y (swap @_ @b @w) . associatorInv @k @b @w @y . (f `par` g))

-- | Note: This is only premonoidal, not monoidal, unless the monoid is commutative.
instance (Monoid (w :: k), SymMonoidal k) => MonoidalProfunctor (Writer w :: k +-> k) where
  par0 = id \\ unitObj @k
  Writer @x2 @x1 f `par` Writer @y2 @y1 g =
    f //
      g //
        withOb2 @_ @x1 @y1 $
          withOb2 @_ @x2 @y2 $
            Writer
              ( associator @k @w @x2 @y2
                  . first @y2 (first @x2 (mappend @w) . associatorInv @k @w @w @x2 . swap' f (obj @w))
                  . associatorInv @k @x1 @w @y2
                  . second @x1 g
              )

-- | A version of traverse specialized to `Writer`, with fewer requirements on @p@.
traverseWriter :: forall {k} p (w :: k). (Strong k p, SelfAction k, Ob w) => Writer w :.: p :~> p :.: Writer w
traverseWriter (Writer f :.: p) = let wp = obj @w `act` p in lmap f wp :.: Writer (tgt wp) \\ wp \\ p

instance (Monoid (w :: k), Monoidal k) => Traversable (Writer w :: k +-> k) where
  traverse = traverseWriter

-- Writer is not Cotraversable

writerComp :: forall {k} (r :: k) (s :: k). (SymMonoidal k, Ob r, Ob s) => Writer r :.: Writer s ~> Writer (r ** s)
writerComp = withOb2 @k @r @s $
  Prof \(Writer f :.: Writer @b g) -> Writer (associatorInv @k @r @s @b . second @r g . f)

writerDay :: forall {k} (r :: k) (s :: k). (SymMonoidal k, Ob r, Ob s) => Writer r `Day` Writer s ~> Writer (r ** s)
writerDay = withOb2 @k @r @s $
  Prof \(Day @_ @d @_ @f f (Writer p) (Writer q) g) -> Writer (second @(r ** s) g . swapInner @r @d @s @f . (p `par` q) . f) \\ g

type WriterT :: k -> k +-> k -> k +-> k
newtype WriterT w p a b where
  WriterT :: (p :.: Writer w) a b -> WriterT w p a b

runWriterT :: (Profunctor p) => WriterT w p a b -> p a (w ** b)
runWriterT (WriterT (p :.: Writer f)) = rmap f p

tell :: (Promonad p, Monoidal k, Ob (w :: k)) => WriterT w p w Unit
tell = WriterT (id :.: Writer rightUnitorInv)

listen :: forall {k} p w a b. (Promonad p, Monoidal k, Comonoid (w :: k)) => WriterT w p a b -> WriterT w p a (w ** b)
listen (WriterT (p :.: Writer f)) = withOb2 @k @w @b $ WriterT (p :.: Writer (associator @k @w @w @b . first @b (comult @w) . f))

censor :: forall {k} p w a b. (Monoidal k, Ob (w :: k)) => w ~> w -> WriterT w p a b -> WriterT w p a b
censor f (WriterT (p :.: Writer w)) = WriterT (p :.: Writer (first @b f . w))

deriving newtype instance (Profunctor p, Monoidal k, Ob (w :: k)) => Profunctor (WriterT w p)
deriving newtype instance (Representable p, Ob (w :: k), Monoidal k) => Representable (WriterT w p)
deriving newtype instance
  (Corepresentable p, Ob (w :: k), SelfAction k, CompactClosed k) => Corepresentable (WriterT w p)
deriving newtype instance (Strong k p, Ob (w :: k), SelfAction k) => Strong k (WriterT w p)
deriving newtype instance
  (MonoidalProfunctor p, Monoid (w :: k), SelfAction k, SymMonoidal k) => MonoidalProfunctor (WriterT w p)
deriving newtype instance (Traversable p, Monoid (w :: k), SelfAction k) => Traversable (WriterT w p)

instance (Monoidal k, Ob w) => Functor (WriterT w :: k +-> k -> k +-> k) where
  map n@Prof{} = Prof \(WriterT p) -> WriterT (unProf (unNat (map n)) p)

instance (Monoidal k) => Functor (WriterT :: k -> k +-> k -> k +-> k) where
  map f = f // Nat $ Prof \(WriterT p) -> WriterT (unProf (map (map f)) p)

instance (Monoid (w :: k), SelfAction k, Strong k p, Promonad p) => Promonad (WriterT w p) where
  id = WriterT (id :.: id)
  WriterT l . WriterT r = WriterT (compComp traverseWriter l r)

-- | WriterT is a monad on profunctors, i.e. we have @p ~> WriterT p@ and @WriterT (WriterT p) ~> WriterT p@.
instance (Monoid w, Monoidal k) => Promonad (Star (WriterT w :: k +-> k -> k +-> k)) where
  id = Star $ Prof \p -> WriterT (p :.: id) \\ p
  Star l . Star r = Star $ Prof (\(WriterT (WriterT (p :.: f) :.: g)) -> WriterT (p :.: (g . f))) . map l . r