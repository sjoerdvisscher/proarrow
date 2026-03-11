{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Simplex (module Proarrow.Category.Instance.Simplex, Nat (..)) where

import Data.Fin (Fin (..))
import Data.Kind (Type)
import Data.Type.Nat (Nat (..), type Plus, SNatI)
import Data.Vec.Lazy (Vec (..))
import Prelude (Eq, Show (..), (++), type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj, src, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Data.Typeable (Typeable)

type n + m = Plus n m

data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: (IsNat n) => SNat (S n)
instance Show (SNat n) where
  show SZ = "Z"
  show (SS @n') = "S" ++ show (singNat @n')

class (a + Z ~ a, a + S b ~ S (a + b), (a + b) + c ~ a + (b + c)) => Rules a b c
instance (a + Z ~ a, a + S b ~ S (a + b), (a + b) + c ~ a + (b + c)) => Rules a b c

class (forall b c. Rules a b c, SNatI a, Typeable a) => IsNat (a :: Nat) where singNat :: SNat a
instance IsNat Z where singNat = SZ
instance (IsNat a) => IsNat (S a) where singNat = SS

type Simplex :: CAT Nat
data Simplex a b where
  ZZ :: Simplex Z Z
  Y :: Simplex x y -> Simplex x (S y)
  X :: Simplex x (S y) -> Simplex (S x) (S y)
deriving instance Eq (Simplex a b)
deriving instance Show (Simplex a b)

suc :: Simplex a b -> Simplex (S a) (S b)
suc = X . Y

-- | The (augmented) simplex category is the category of finite ordinals and order preserving maps.
instance CategoryOf Nat where
  type (~>) = Simplex
  type Ob a = IsNat a

instance Promonad Simplex where
  id @a = case singNat @a of
    SZ -> ZZ
    SS -> suc id
  ZZ . f = f
  Y f . g = Y (f . g)
  X f . Y g = f . g
  X f . X g = X (X f . g)

instance Profunctor Simplex where
  dimap = dimapDefault
  r \\ ZZ = r
  r \\ Y f = r \\ f
  r \\ X f = r \\ f

instance HasInitialObject Nat where
  type InitialObject = Z
  initiate @a = case singNat @a of
    SZ -> ZZ
    SS @a' -> Y (initiate @_ @a')

instance HasTerminalObject Nat where
  type TerminalObject = S Z
  terminate @a = case singNat @a of
    SZ -> Y ZZ
    SS @n -> X (terminate @_ @n)

data family Forget :: Nat +-> Type
instance FunctorForRep Forget where
  type Forget @ n = Fin n
  fmap ZZ = id
  fmap (Y f) = FS . fmap @Forget f
  fmap (X f) = \case
    FZ -> FZ
    FS n -> fmap @Forget f n

data family Pick :: Type -> OPPOSITE Nat +-> Type
instance FunctorForRep (Pick a) where
  type (Pick a) @ OP n = Vec n a
  fmap (Op ZZ) VNil = VNil
  fmap (Op (Y f)) (_ ::: xs) = fmap @(Pick a) (Op f) xs
  fmap (Op (X f)) (x ::: xs) = x ::: (fmap @(Pick a) (Op f) (x ::: xs))

instance MonoidalProfunctor Simplex where
  par0 = ZZ
  ZZ `par` g = g
  Y f `par` g = Y (f `par` g)
  X f `par` g = X (f `par` g)

-- | Addition as monoidal tensor.
instance Monoidal Nat where
  type Unit = Z
  type a ** b = a + b
  withOb2 @a @b r = case singNat @a of
    SZ -> r
    SS @a' -> withOb2 @_ @a' @b r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @a @b @c = withOb2 @_ @a @b (withOb2 @_ @(a ** b) @c (id @Simplex))
  associatorInv @a @b @c = withOb2 @_ @b @c (withOb2 @_ @a @(b ** c) (id @Simplex))

-- Not symmetric monoidal

instance Monoid Z where
  mempty = ZZ
  mappend = ZZ

instance Monoid (S Z) where
  mempty = Y ZZ
  mappend = X (X (Y ZZ))

data family Replicate :: k -> Nat +-> k
instance (Monoid m) => FunctorForRep (Replicate m) where
  type Replicate m @ Z = Unit
  type Replicate m @ S b = m ** (Replicate m @ b)
  fmap ZZ = par0
  fmap (Y f) = let g = fmap @(Replicate m) f in (mempty @m `par` g) . leftUnitorInv \\ g
  fmap (X (Y f)) = obj @m `par` fmap @(Replicate m) f
  fmap (X (X @x f)) =
    let g = fmap @(Replicate m) (X f)
        b = fmap @(Replicate m) (src f)
    in g . (mappend @m `par` b) . associatorInv @_ @m @m @(Replicate m @ x) \\ b
