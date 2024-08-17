module Proarrow.Category.Instance.Simplex where

import Data.Kind (Type, Constraint)

import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj, PRO, Profunctor (..), Promonad (..), dimapDefault, obj, src, tgt)
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)
-- import Proarrow.Category.Bicategory qualified as B

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
  ZZ :: Simplex Z Z
  Y :: Simplex x y -> Simplex x (S y)
  X :: Simplex x (S y) -> Simplex (S x) (S y)

suc :: Simplex a b -> Simplex (S a) (S b)
suc = X . Y

instance CategoryOf Nat where
  type (~>) = Simplex
  type Ob a = IsNat a

instance Promonad Simplex where
  id :: forall a. (Ob a) => Simplex a a
  id = singObj (singNat @a)
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
  initiate' a = go (singNat' a)
    where
      go :: SNat b -> Simplex Z b
      go SZ = ZZ
      go (SS n) = Y (go n)

instance HasTerminalObject Nat where
  type TerminalObject = S Z
  terminate' a = go (singNat' a)
    where
      go :: SNat b -> Simplex b (S Z)
      go SZ = Y ZZ
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
  repMap ZZ = id
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
  ZZ `par` g = g
  Y f `par` g = Y (f `par` g)
  X f `par` g = X (f `par` g)
  leftUnitor f = f
  leftUnitorInv f = f
  rightUnitor f = f . rightUnitor' (singNat' (src f))
  rightUnitorInv f = rightUnitorInv' (singNat' (tgt f)) . f
  associator a' b' = associator' (singNat' a') (singNat' b')
  associatorInv a' b' = associatorInv' (singNat' a') (singNat' b')

rightUnitor' :: SNat b -> Simplex (b + Z) b
rightUnitor' SZ = ZZ
rightUnitor' (SS n) = suc (rightUnitor' n)

rightUnitorInv' :: SNat b -> Simplex b (b + Z)
rightUnitorInv' SZ = ZZ
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
  mempty = Y ZZ
  mappend = X (X (Y ZZ))

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
  repMap ZZ = obj @Unit
  repMap (Y f) = let g = repMap @(Replicate m) f in (mempty @m `par` g) . leftUnitorInv (src g)
  repMap (X (Y f)) = obj @m `par` repMap @(Replicate m) f
  repMap (X (X f)) =
    let g = repMap @(Replicate m) (X f)
        b = repMap @(Replicate m) (src f)
    in g . (mappend @m `par` b) . associatorInv (obj @m) (obj @m) b


class IsSimplex s where
  bisimplex :: BiSimplex s s
instance IsSimplex ZZ where
  bisimplex = ZZZ
instance (IsSimplex s) => IsSimplex (Y s) where
  bisimplex = YYY bisimplex
instance (IsSimplex s) => IsSimplex (X s) where
  bisimplex = XXX bisimplex

type LT :: forall j k -> Simplex j k -> Simplex j k -> Constraint
type family LT j k (f :: Simplex j k) (g :: Simplex j k) :: Constraint where
  LT Z Z ZZ ZZ = ()
  LT j (S k) (Y f) (Y g) = LT j k f g
  LT (S j) (S k) (X f) (X g) = LT j (S k) f g

type (f :: Simplex j k) <= g = LT j k f g

type BiSimplex :: CAT (Simplex j k)
data BiSimplex f g where
  ZZZ :: BiSimplex ZZ ZZ
  YYY :: BiSimplex f g -> BiSimplex (Y f) (Y g)
  XXX :: BiSimplex f g -> BiSimplex (X f) (X g)

instance Profunctor BiSimplex where
  dimap = dimapDefault
  r \\ ZZZ = r
  r \\ YYY f = r \\ f
  r \\ XXX f = r \\ f
instance Promonad BiSimplex where
  id :: forall a. (Ob a) => BiSimplex a a
  id = bisimplex @a
  ZZZ . f = f
  YYY f . YYY g = YYY (f . g)
  XXX f . XXX g = XXX (f . g)
instance CategoryOf (Simplex j k) where
  type (~>) = BiSimplex
  type Ob a = IsSimplex a

type family SimplexI :: Simplex i i
type instance SimplexI @Z = ZZ
type instance SimplexI @(S n) = X (Y (SimplexI @n))

type family SimplexO (f :: Simplex i j) (g :: Simplex j k) :: Simplex i k
type instance SimplexO f ZZ = f
type instance SimplexO f (Y g) = Y (SimplexO f g)
type instance SimplexO (Y f) (X g) = SimplexO f g
type instance SimplexO (X f) (X g) = X (SimplexO f (X g))

-- instance B.Bicategory Simplex where
--   type Ob0 Simplex n = IsNat n
--   type I = SimplexI
--   type a `O` b = SimplexO a b
--   iObj :: forall i. B.Ob0 Simplex i => Obj (B.I :: Simplex i i)
--   iObj = go (singNat @i) where
--     go :: SNat n -> Obj (B.I :: Simplex n n)
--     go SZ = ZZZ
--     go (SS n) = XXX (YYY (go n))
--   ZZZ `o` ZZZ = ZZZ