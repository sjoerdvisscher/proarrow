module Proarrow.Promonad.State where

import Prelude (($))

import Proarrow.Adjunction qualified as Adj
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), swap', leftUnitorWith)
import Proarrow.Category.Monoidal.Action (SelfAction, Strong (..))
import Proarrow.Category.Opposite (OPPOSITE (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), arr, obj, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Object (ObjDict (..), objDicts)
import Proarrow.Object.Dual (CompactClosed)
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Promonad.Reader (Reader (..))
import Proarrow.Promonad.Writer (Writer (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Object.BinaryProduct ((&&&))
import Proarrow.Monoid (Comonoid (..))

type State s = StateT s Id
pattern State :: forall {k} a b s. (Monoidal k, Ob (s :: k)) => (Ob a, Ob b) => (s ** a) ~> (s ** b) -> State s a b
pattern State f <- (runStateT &&& objDicts -> (Id f, (ObjDict, ObjDict)))
  where
    State f = StateT (Reader id :.: Id f :.: Writer id) \\ f
{-# COMPLETE State #-}

-- | Note: This is only premonoidal, not monoidal.
instance (SymMonoidal k, Ob s) => MonoidalProfunctor (State (s :: k)) where
  par0 = State (obj @s `par` par0) \\ (par0 :: (Unit :: k) ~> Unit)
  par (State @a1 @b1 f) (State @a2 @b2 g) =
    let s = obj @s; a1 = obj @a1; b1 = obj @b1; a2 = obj @a2; b2 = obj @b2
    in State
         ( (s `par` swap' b2 b1)
             . associator @_ @s @b2 @b1
             . (g `par` b1)
             . associatorInv @_ @s @a2 @b1
             . (s `par` swap' b1 a2)
             . associator @_ @s @b1 @a2
             . (f `par` a2)
             . associatorInv @_ @s @a1 @a2
         )
         \\ (a1 `par` a2)
         \\ (b1 `par` b2)

type StateT :: k -> k +-> k -> k +-> k
newtype StateT s p a b where
  StateT :: (Reader (OP s) :.: p :.: Writer s) a b -> StateT s p a b

runStateT :: (Profunctor p) => StateT s p a b -> p (s ** a) (s ** b)
runStateT (StateT (Reader f :.: p :.: Writer g)) = dimap f g p

get :: forall {k} p s. (Promonad p, Monoidal k, Comonoid (s :: k)) => StateT s p Unit s
get = StateT (Reader (rightUnitor @k @s) :.: id :.: Writer (comult @s))

put :: forall {k} p s. (Promonad p, Monoidal k, Comonoid (s :: k)) => StateT s p s Unit
put = StateT (Reader (leftUnitorWith (counit @s)) :.: id :.: Writer (rightUnitorInv @k @s))

deriving newtype instance (Profunctor p, Monoidal k, Ob (s :: k)) => Profunctor (StateT s p)
deriving newtype instance (Representable p, Ob (s :: k), SymMonoidal k, Closed k) => Representable (StateT s p)
deriving newtype instance
  (Corepresentable p, Ob (s :: k), SelfAction k, CompactClosed k) => Corepresentable (StateT s p)
deriving newtype instance (Strong k p, Ob (s :: k), SelfAction k) => Strong k (StateT s p)

instance (Ob (s :: k), SelfAction k, Strong k p, Promonad p) => Promonad (StateT s p) where
  id @a = withOb2 @k @s @a $ StateT (Reader id :.: act (obj @s) (id @p @a) :.: Writer id)
  StateT (r1 :.: p1 :.: w1) . StateT (r2 :.: p2 :.: w2) = StateT (r2 :.: (p1 . arr (Adj.counit (w2 :.: r1)) . p2) :.: w1)

instance (Monoidal k, Ob s) => Functor (StateT s :: k +-> k -> k +-> k) where
  map (Prof n) = Prof \(StateT (r :.: p :.: w)) -> StateT (r :.: n p :.: w)
