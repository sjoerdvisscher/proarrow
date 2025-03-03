module Proarrow.Category.Instance.Lifted (LIFTED (..), Lift (..), LIFTEDF, pattern LiftF) where

import Proarrow.Adjunction (Adjunction, unit')
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core
import Proarrow.Functor (Functor)
import Proarrow.Object (pattern Obj)
import Proarrow.Object.BinaryCoproduct (Coprod, HasBinaryCoproducts (..), codiag, copar)
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..), diag)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Star (Star (..))

newtype LIFTED (p :: j +-> k) (q :: k +-> j) = LIFT j
type instance UN LIFT (LIFT j) = j

-- | A category lifted by an adjunction.
data Lift a b where
  Lift :: (q :.: p) a b -> Lift (LIFT a :: LIFTED p q) (LIFT b)

instance (Adjunction p q) => Profunctor (Lift :: CAT (LIFTED p q)) where
  dimap = dimapDefault
  r \\ Lift pq = r \\ pq
instance (Adjunction p q) => Promonad (Lift :: CAT (LIFTED p q)) where
  id = Lift id
  Lift f . Lift g = Lift (f . g)
instance (Adjunction p q) => CategoryOf (LIFTED p q) where
  type (~>) = Lift
  type Ob (a :: LIFTED p q) = (Is LIFT a, Ob (UN LIFT a))

instance (Adjunction (p :: j +-> k) (q :: k +-> j), HasTerminalObject j) => HasTerminalObject (LIFTED p q) where
  type TerminalObject = LIFT TerminalObject
  terminate = Lift (unit' terminate)

instance
  (Adjunction (p :: j +-> k) (q :: k +-> j), MonoidalProfunctor p, MonoidalProfunctor q, Cartesian j)
  => HasBinaryProducts (LIFTED p q)
  where
  type LIFT a && LIFT b = LIFT (a && b)
  withObProd @(LIFT a) @(LIFT b) = withObProd @j @a @b
  fst @(LIFT a) @(LIFT b) = Lift (unit' (fst @j @a @b))
  snd @(LIFT a) @(LIFT b) = Lift (unit' (snd @j @a @b))
  Lift (ql :.: pl) &&& Lift (qr :.: pr) = Lift (lmap diag (ql `par` qr) :.: (pl `par` pr)) \\ ql

instance (Adjunction (p :: j +-> k) (q :: k +-> j), HasInitialObject j) => HasInitialObject (LIFTED p q) where
  type InitialObject = LIFT InitialObject
  initiate = Lift (unit' initiate)

instance
  ( Adjunction (p :: j +-> k) (q :: k +-> j)
  , MonoidalProfunctor (Coprod p)
  , MonoidalProfunctor (Coprod q)
  , HasBinaryCoproducts j
  )
  => HasBinaryCoproducts (LIFTED p q)
  where
  type LIFT a || LIFT b = LIFT (a || b)
  withObCoprod @(LIFT a) @(LIFT b) = withObCoprod @j @a @b
  lft @(LIFT a) @(LIFT b) = Lift (unit' (lft @j @a @b))
  rgt @(LIFT a) @(LIFT b) = Lift (unit' (rgt @j @a @b))
  Lift (ql :.: pl) ||| Lift (qr :.: pr) = Lift ((ql `copar` qr) :.: rmap codiag (pl `copar` pr)) \\ pl

-- | Categories lifted by a functor: @f a ~> f b@.
type LIFTEDF (f :: j -> k) = LIFTED (Star f) (Costar f)

unlift :: (Functor f) => Lift (LIFT a :: LIFTEDF f) (LIFT b) -> (f a ~> f b, Obj a, Obj b)
unlift (Lift (Costar f :.: Star g)) = (g . f, Obj, Obj)

pattern LiftF :: (Functor f) => (Ob a, Ob b) => (f a ~> f b) -> Lift (LIFT a :: LIFTEDF f) (LIFT b)
pattern LiftF f <- (unlift -> (f, Obj, Obj))
  where
    LiftF f = Lift (Costar f :.: Star id)

{-# COMPLETE LiftF #-}