module Proarrow.Promonad.Reader where

import Prelude (($))

import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , first
  , second
  , swap'
  , unitObj
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..), strongPar0)
import Proarrow.Category.Monoidal.Distributive (Cotraversable (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, rmap, src, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..), comultAct, counitAct, mappendAct, memptyAct)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Promonad.Writer (Writer (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))

data Reader r a b where
  Reader :: forall a b r. (Ob a) => Act r a ~> b -> Reader (OP r) a b

instance (Ob (r :: m), MonoidalAction m k) => Profunctor (Reader (OP r) :: k +-> k) where
  dimap l r (Reader f) = Reader (r . f . (act (obj @r) l)) \\ r \\ l
  r \\ Reader f = r \\ f

instance (Ob (r :: m), MonoidalAction m k) => Corepresentable (Reader (OP r) :: k +-> k) where
  type Reader (OP r) %% a = Act r a
  coindex (Reader f) = f
  cotabulate f = Reader f
  corepMap f = act (obj @r) f

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
      \\ g

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
  cotraverse (p :.: Reader f) = let rp = strongPar0 @r `act` p in Reader (src rp) :.: rmap f rp \\ rp \\ p

instance (Ob (r :: m), MonoidalAction m k) => Proadjunction (Writer r :: k +-> k) (Reader (OP r)) where
  unit @a = Reader id :.: Writer id \\ act (obj @r) (obj @a)
  counit (Writer f :.: Reader g) = g . f
