module Proarrow.Promonad.Reader where

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , first
  , obj2
  , second
  , swap'
  , unitObj
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..), comultAct, counitAct, mappendAct, memptyAct)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Promonad.Writer (Writer (..))

data Reader r a b where
  Reader :: (Ob a, Ob b) => Act r a ~> b -> Reader (OP r) a b

instance (Ob (r :: m), MonoidalAction m k) => Profunctor (Reader (OP r) :: k +-> k) where
  dimap l r (Reader f) = Reader (r . f . (act (obj @r) l)) \\ r \\ l
  r \\ Reader f = r \\ f

instance (MonoidalAction m k) => Functor (Reader :: OPPOSITE m -> k +-> k) where
  map (Op f) = f // Prof \(Reader @a g) -> Reader (g . act f (obj @a))

instance (Comonoid (r :: m), MonoidalAction m k) => Promonad (Reader (OP r) :: k +-> k) where
  id = Reader (counitAct @r)
  Reader g . Reader @a f = Reader (g . act (obj @r) f . comultAct @r @a)

instance (Monoid (r :: m), MonoidalAction m k) => Procomonad (Reader (OP r) :: k +-> k) where
  extract (Reader f) = f . memptyAct @r
  duplicate (Reader @a f) = Reader id :.: Reader (f . mappendAct @r @a) \\ f

instance (Ob (r :: m), MonoidalAction m k, SymMonoidal m) => Strong m (Reader (OP r) :: k +-> k) where
  act @a @b @x @y f (Reader g) =
    Reader (act f g . multiplicatorInv @m @k @a @r @x . act (swap @_ @r @a) (obj @x) . multiplicator @m @k @r @a @x)
      \\ act (obj @a) (obj @x)
      \\ act (obj @b) (obj @y)
      \\ f

instance (Comonoid (r :: k), SelfAction k, SymMonoidal k) => MonoidalProfunctor (Reader (OP r) :: k +-> k) where
  par0 = id \\ unitObj @k
  Reader @x1 @x2 f `par` Reader @y1 @y2 g =
    Reader
      ( second @x2 g
          . associator @k @x2 @r @y1
          . ((swap' (obj @r) f . associator @k @r @r @x1 . first @x1 (comult @r)) `par` obj @y1)
          . associatorInv @k @r @x1 @y1
      )
      \\ obj2 @x1 @y1
      \\ obj2 @x2 @y2

instance (Ob (r :: m), MonoidalAction m k) => Adjunction (Writer r :: k +-> k) (Reader (OP r)) where
  unit @a = Reader id :.: Writer id \\ act (obj @r) (obj @a)
  counit (Writer f :.: Reader g) = g . f