module Proarrow.Category.Instance.Simplex where

import Data.Kind (Type)

import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj, PRO, Profunctor (..), Promonad (..), dimapDefault, obj, src)
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

type data Nat = Z | S Nat
data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

class IsNat (a :: Nat) where
  singNat :: SNat a
instance IsNat Z where singNat = SZ
instance (IsNat a) => IsNat (S a) where singNat = SS singNat

singNat' :: forall a. Obj a -> SNat a
singNat' a = singNat @a \\ a

singObj :: SNat a -> Obj a
singObj SZ = obj
singObj (SS n) = suc (singObj n)

type Simplex :: CAT Nat
data Simplex a b where
  Z :: Simplex Z Z
  Y :: Simplex x y -> Simplex x (S y)
  X :: Simplex x (S y) -> Simplex (S x) (S y)

suc :: Simplex a b -> Simplex (S a) (S b)
suc = X . Y

instance CategoryOf Nat where
  type (~>) = Simplex
  type Ob a = IsNat a

instance Promonad Simplex where
  id :: forall a. (Ob a) => Simplex a a
  id = go (singNat @a)
    where
      go :: SNat b -> Simplex b b
      go SZ = Z
      go (SS n) = suc (go n)
  Z . f = f
  f . Z = f
  Y f . g = Y (f . g)
  X f . Y g = f . g
  X f . X g = X (X f . g)

instance Profunctor Simplex where
  dimap = dimapDefault
  r \\ Z = r
  r \\ Y f = r \\ f
  r \\ X f = r \\ f

instance HasInitialObject Nat where
  type InitialObject = Z
  initiate' a = go (singNat' a)
    where
      go :: SNat b -> Simplex Z b
      go SZ = Z
      go (SS n) = Y (go n)

instance HasTerminalObject Nat where
  type TerminalObject = S Z
  terminate' a = go (singNat' a)
    where
      go :: SNat b -> Simplex b (S Z)
      go SZ = Y Z
      go (SS n) = X (go n)

data Fin :: Nat -> Type where
  Fz :: Fin (S n)
  Fs :: Fin n -> Fin (S n)

type Forget :: PRO Type Nat
data Forget a b where
  Forget :: (Ob b) => {getForget :: a -> Fin b} -> Forget a b

instance Profunctor Forget where
  dimap = dimapRep
  r \\ Forget f = r \\ f
instance Representable Forget where
  type Forget % n = Fin n
  index = getForget
  tabulate = Forget
  repMap Z = id
  repMap (Y f) = Fs . repMap @Forget f
  repMap (X f) = \case
    Fz -> Fz
    Fs n -> repMap @Forget f n

type family (a :: Nat) + (b :: Nat) :: Nat where
  Z + b = b
  S a + b = S (a + b)

instance Monoidal Nat where
  type Unit = Z
  type a ** b = a + b
  Z `par` g = g
  Y f `par` g = Y (f `par` g)
  X f `par` g = X (f `par` g)
  leftUnitor a = a
  leftUnitorInv a = a
  rightUnitor = rightUnitor' . singNat'
  rightUnitorInv = rightUnitorInv' . singNat'
  associator a' b' = associator' (singNat' a') (singNat' b')
  associatorInv a' b' = associatorInv' (singNat' a') (singNat' b')

rightUnitor' :: SNat b -> Simplex (b + Z) b
rightUnitor' SZ = Z
rightUnitor' (SS n) = suc (rightUnitor' n)

rightUnitorInv' :: SNat b -> Simplex b (b + Z)
rightUnitorInv' SZ = Z
rightUnitorInv' (SS n) = suc (rightUnitorInv' n)

associator' :: SNat a -> SNat b -> Obj c -> Simplex ((a + b) + c) (a + (b + c))
associator' SZ SZ c = c
associator' SZ (SS b) c = suc (associator' SZ b c)
associator' (SS a) b c = suc (associator' a b c)

associatorInv' :: SNat a -> SNat b -> Obj c -> Simplex (a + (b + c)) ((a + b) + c)
associatorInv' SZ SZ c = c
associatorInv' SZ (SS b) c = suc (associatorInv' SZ b c)
associatorInv' (SS a) b c = suc (associatorInv' a b c)

instance Monoid (S Z) where
  mempty = Y Z
  mappend = X (X (Y Z))

type Replicate :: k -> PRO k Nat
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
  repMap Z = obj @Unit
  repMap (Y f) = let g = repMap @(Replicate m) f in (mempty @m `par` g) . leftUnitorInv (src g)
  repMap (X (Y f)) = obj @m `par` repMap @(Replicate m) f
  repMap (X (X f)) =
    let g = repMap @(Replicate m) (X f)
        b = repMap @(Replicate m) (src f)
    in g . (mappend @m `par` b) . associatorInv (obj @m) (obj @m) b
