{-# LANGUAGE TupleSections #-}

module Proarrow.Promonad.Writer where

import Prelude (($))

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
  , unitObj, swapInner
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..), strongPar0)
import Proarrow.Category.Monoidal.Distributive (Traversable (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, obj, tgt, (//), type (+->))
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
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Profunctor.Day (Day(..))

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

instance (Monoid (w :: k), Monoidal k) => Traversable (Writer w :: k +-> k) where
  traverse (Writer f :.: p) = let wp = unId (strongPar0 @w) `act` p in lmap f wp :.: Writer (tgt wp) \\ wp \\ p

writerComp :: forall {k} (r :: k) (s :: k). (SymMonoidal k, Ob r, Ob s) => Writer r :.: Writer s ~> Writer (r ** s)
writerComp = withOb2 @k @r @s $
  Prof \(Writer f :.: Writer @b g) -> Writer (associatorInv @k @r @s @b . second @r g . f)

writerDay :: forall {k} (r :: k) (s :: k). (SymMonoidal k, Ob r, Ob s) => Writer r `Day` Writer s ~> Writer (r ** s)
writerDay = withOb2 @k @r @s $
  Prof \(Day @_ @d @_ @f f (Writer p) (Writer q) g) -> Writer (second @(r ** s) g . swapInner @r @d @s @f . (p `par` q) . f) \\ g