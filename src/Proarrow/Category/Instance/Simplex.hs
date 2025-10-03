{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Simplex where

import Data.Kind (Type)

import Prelude (Eq, Show (..), (++), type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj, src, type (+->))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (FunctorForRep (..), Representable (..), dimapRep)

type data Nat = Z | S Nat
data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: (IsNat n) => SNat (S n)
instance Show (SNat n) where
  show SZ = "Z"
  show (SS @n') = "S" ++ show (singNat @n')

class (a + Z ~ a, a + S b ~ S (a + b), (a + b) + c ~ a + (b + c)) => Rules a b c
instance (a + Z ~ a, a + S b ~ S (a + b), (a + b) + c ~ a + (b + c)) => Rules a b c

class (forall b c. Rules a b c) => IsNat (a :: Nat) where singNat :: SNat a
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

data Fin :: Nat -> Type where
  Fz :: Fin (S n)
  Fs :: Fin n -> Fin (S n)

data family Forget :: Nat +-> Type
instance FunctorForRep Forget where
  type Forget @ n = Fin n
  fmap ZZ = id
  fmap (Y f) = Fs . fmap @Forget f
  fmap (X f) = \case
    Fz -> Fz
    Fs n -> fmap @Forget f n

type family (a :: Nat) + (b :: Nat) :: Nat where
  Z + b = b
  S a + b = S (a + b)

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

instance Monoid Z where
  mempty = ZZ
  mappend = ZZ

instance Monoid (S Z) where
  mempty = Y ZZ
  mappend = X (X (Y ZZ))

type Replicate :: k -> Nat +-> k
data Replicate m a b where
  Replicate :: (Ob b) => a ~> (Replicate m % b) -> Replicate m a b
instance (Monoid m) => Profunctor (Replicate m) where
  dimap = dimapRep
  r \\ Replicate f = r \\ f
instance (Monoid m) => Representable (Replicate m) where
  type Replicate m % Z = Unit
  type Replicate m % S b = m ** (Replicate m % b)
  index (Replicate f) = f
  tabulate = Replicate
  repMap ZZ = par0
  repMap (Y f) = let g = repMap @(Replicate m) f in (mempty @m `par` g) . leftUnitorInv \\ g
  repMap (X (Y f)) = obj @m `par` repMap @(Replicate m) f
  repMap (X (X @x f)) =
    let g = repMap @(Replicate m) (X f)
        b = repMap @(Replicate m) (src f)
    in g . (mappend @m `par` b) . associatorInv @_ @m @m @(Replicate m % x) \\ b
