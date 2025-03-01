{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Instance.Simplex where

import Data.Kind (Constraint, Type)

import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj, PRO, Profunctor (..), Promonad (..), dimapDefault, obj, src)
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

type data Nat = Z | S Nat
data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

class (a + Z ~ a) => IsNat (a :: Nat) where
  singNat :: SNat a
  withIsNat2 :: IsNat b => (IsNat (a + b) => r) -> r
instance IsNat Z where
  singNat = SZ
  withIsNat2 r = r
instance (IsNat a) => IsNat (S a) where
  singNat = SS singNat
  withIsNat2 @b r = withIsNat2 @a @b r

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
  initiate' ZZ = ZZ
  initiate' (Y n) = Y (initiate' n)
  initiate' (X n) = initiate' n

instance HasTerminalObject Nat where
  type TerminalObject = S Z
  terminate' ZZ = Y ZZ
  terminate' (Y n) = terminate' n
  terminate' (X n) = X (terminate' n)

data Fin :: Nat -> Type where
  Fz :: Fin (S n)
  Fs :: Fin n -> Fin (S n)

type Forget :: PRO Type Nat
data Forget a b where
  Forget :: (Ob b) => {unForget :: a -> Fin b} -> Forget a b

instance Profunctor Forget where
  dimap = dimapRep
  r \\ Forget f = r \\ f
instance Representable Forget where
  type Forget % n = Fin n
  index = unForget
  tabulate = Forget
  repMap ZZ = id
  repMap (Y f) = Fs . repMap @Forget f
  repMap (X f) = \case
    Fz -> Fz
    Fs n -> repMap @Forget f n

type family (a :: Nat) + (b :: Nat) :: Nat where
  Z + b = b
  S a + b = S (a + b)

instance MonoidalProfunctor Simplex where
  par0 = ZZ
  ZZ `par` g = g
  Y f `par` g = Y (f `par` g)
  X f `par` g = X (f `par` g)

instance Monoidal Nat where
  type Unit = Z
  type a ** b = a + b
  withOb2 @a @b = withIsNat2 @a @b
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @a @b @c = associator' (singNat @a) (singNat @b) (obj @c)
  associatorInv @a @b @c = associatorInv' (singNat @a) (singNat @b) (obj @c)

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
  repMap ZZ = par0
  repMap (Y f) = let g = repMap @(Replicate m) f in (mempty @m `par` g) . leftUnitorInv \\ g
  repMap (X (Y f)) = obj @m `par` repMap @(Replicate m) f
  repMap (X (X @x f)) =
    let g = repMap @(Replicate m) (X f)
        b = repMap @(Replicate m) (src f)
    in g . (mappend @m `par` b) . associatorInv @_ @m @m @(Replicate m % x) \\ b

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
