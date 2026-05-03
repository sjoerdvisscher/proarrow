{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.FinRel where

import Data.Fin (Fin (..))
import Data.Type.Nat (Mult, Nat (..), Nat0, Nat1, Plus, SNat (..), SNatI, snat, snatToNatural)
import Data.Vec.Lazy (Vec (..), chunks, concatMap, repeat, universe, zipWith, (++))
import GHC.Bits qualified as B
import GHC.Natural (Natural)
import Prelude (Bounded, Enum (..), Eq, Num (..), Ord, Show, divMod, fromIntegral, ($))
import Prelude qualified as P

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (Costrong (..), MonoidalAction (..), Strong (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Monoidal.Hypergraph (Frobenius (..), Hypergraph, spiderDefault)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), HasBiproducts, Coprod (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Dual (CompactClosed (..), ExpSA, StarAutonomous (..), applySA, coactCC, currySA, expSA)
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (Rep (..))

newtype Bitstring (n :: Nat) = BS Natural
  deriving (Eq, Ord)
  deriving newtype (Num, B.Bits)

instance (SNatI n) => Bounded (Bitstring n) where
  minBound = BS 0
  maxBound = BS (shiftN @n 1 - 1)
instance Enum (Bitstring n) where
  fromEnum (BS x) = fromIntegral x
  toEnum x = BS (fromIntegral x)
instance (SNatI n) => Show (Bitstring n) where
  show n = case snat @n of
    SZ -> ""
    SS -> case pop n of (n', b) -> (if b then "1" else "0") P.++ P.show n'

shiftN :: forall n. (SNatI n) => Natural -> Natural
shiftN n = n `B.shiftL` fromIntegral (snatToNatural (snat @n))

-- | Split n + m bits into two parts: the lower n bits and the higher m bits.
split :: (SNatI n) => Bitstring (Plus n m) -> (Bitstring n, Bitstring m)
split @n (BS x) = case (x `divMod` (shiftN @n 1)) of (m, n) -> (BS n, BS m)

splits :: forall n m. (SNatI n, SNatI m) => Bitstring (Mult n m) -> Vec n (Bitstring m)
splits bs = case snat @n of
  SZ -> VNil
  SS -> case split @m bs of
    (v, vs) -> v ::: splits vs

-- | Combine two bitstrings of lengths n and m into one bitstring with the n lower bits or m higher bits.
combine :: (SNatI n) => Bitstring n -> Bitstring m -> Bitstring (Plus n m)
combine @n (BS x) (BS y) = BS ((shiftN @n y) B..|. x)

combines :: (SNatI m) => Vec n (Bitstring m) -> Bitstring (Mult n m)
combines VNil = 0
combines (v ::: vs) = combine v (combines vs)

pop :: Bitstring (S n) -> (Bitstring n, P.Bool)
pop (BS n) = (BS (n `B.shiftR` 1), B.testBit n 0)

push :: P.Bool -> Bitstring n -> Bitstring (S n)
push b (BS n) = BS (n * 2 + if b then 1 else 0)

mult :: forall n m. (SNatI n, SNatI m) => Bitstring n -> Bitstring m -> Bitstring (Mult n m)
mult n m = case snat @n of
  SZ -> 0
  SS -> case pop n of (n', b) -> combine (if b then m else 0) (mult n' m)

bit :: (SNatI n) => Fin n -> Bitstring n
bit = B.bit . fromEnum

zero :: (SNatI n, SNatI m) => Vec n (Bitstring m)
zero = repeat 0

pick :: forall n a. Vec n a -> Bitstring n -> [a]
pick VNil _ = []
pick (a ::: as) n = case pop n of (n', b) -> (if b then (a :) else id) (pick as n')

fromBools :: forall n. Vec n P.Bool -> Bitstring n
fromBools VNil = 0
fromBools (b ::: bs) = push b (fromBools bs)

toBools :: forall n. (SNatI n) => Bitstring n -> Vec n P.Bool
toBools n = case snat @n of
  SZ -> VNil
  SS -> case pop n of (n', b) -> b ::: toBools n'

arr :: forall n m. FinSet (FS m) (FS n) -> FinRel (FR m) (FR n)
arr (FinSet v) = FinRel (P.fmap bit v)

type data FINREL = FR Nat
type instance UN FR (FR n) = n

type FinRel :: CAT FINREL
data FinRel a b where
  FinRel :: (SNatI n, SNatI m) => {unFinRel :: Vec n (Bitstring m)} -> FinRel (FR n) (FR m)

deriving instance P.Show (FinRel a b)
deriving instance P.Eq (FinRel a b)

instance Profunctor FinRel where
  dimap = dimapDefault
  r \\ FinRel{} = r
instance Promonad FinRel where
  id = FinRel (P.fmap bit universe)
  FinRel l . FinRel r = FinRel (P.fmap (P.foldr (B..|.) 0 . pick l) r)
instance CategoryOf FINREL where
  type (~>) = FinRel
  type Ob a = (Is FR a, SNatI (UN FR a))

instance DaggerProfunctor FinRel where
  dagger (FinRel v) = FinRel (fromBools P.<$> P.traverse toBools v)

instance HasInitialObject FINREL where
  type InitialObject = FR Nat0
  initiate = FinRel VNil
instance HasBinaryCoproducts FINREL where
  type FR a || FR b = FR (Plus a b)
  withObCoprod @(FR a) @b r = case snat @a of
    SZ -> r
    SS @a' -> withObCoprod @_ @(FR a') @b r
  lft @(FR a) @(FR b) = withObCoprod @_ @(FR a) @(FR b) $ FinRel (P.fmap ((\a -> combine @a @b a 0) . bit) universe)
  rgt @(FR a) @(FR b) = withObCoprod @_ @(FR a) @(FR b) $ FinRel (P.fmap ((\b -> combine @a @b 0 b) . bit) universe)
  FinRel @a l ||| FinRel @b r = withObCoprod @_ @(FR a) @(FR b) $ FinRel (l ++ r)

instance HasTerminalObject FINREL where
  type TerminalObject = FR Nat0
  terminate = FinRel (repeat 0)
instance HasBinaryProducts FINREL where
  type a && b = FR (Plus (UN FR a) (UN FR b))
  withObProd @a @b r = withObCoprod @_ @a @b r
  fst @(FR a) @(FR b) = withObProd @_ @(FR a) @(FR b) $ FinRel (unFinRel (obj @(FR a)) ++ zero @b @a)
  snd @(FR a) @(FR b) = withObProd @_ @(FR a) @(FR b) $ FinRel (zero @a @b ++ unFinRel (obj @(FR b)))
  FinRel @_ @a l &&& FinRel @_ @b r = withObProd @_ @(FR a) @(FR b) $ FinRel (zipWith combine l r)

instance HasBiproducts FINREL

instance MonoidalProfunctor FinRel where
  par0 = id
  FinRel @nl @ml l `par` FinRel @nr @mr r =
    withOb2 @_ @(FR nl) @(FR nr) $
      withOb2 @_ @(FR ml) @(FR mr) $
        FinRel (concatMap (\l' -> P.fmap (mult l') r) l)

instance Monoidal FINREL where
  type FR a ** FR b = FR (Mult a b)
  type Unit = FR Nat1
  withOb2 @(FR a) @b r = case snat @a of
    SZ -> r
    SS @a' -> withOb2 @_ @(FR a') @b $ withObCoprod @_ @b @(FR (Mult a' (UN FR b))) r
  leftUnitor = arr leftUnitor
  leftUnitorInv = arr leftUnitorInv
  rightUnitor = arr rightUnitor
  rightUnitorInv = arr rightUnitorInv
  associator @(FR a) @(FR b) @(FR c) = arr (associator @_ @(FS a) @(FS b) @(FS c))
  associatorInv @(FR a) @(FR b) @(FR c) = arr (associatorInv @_ @(FS a) @(FS b) @(FS c))

instance SymMonoidal FINREL where
  swap @(FR a) @(FR b) = arr (swap @_ @(FS a) @(FS b))

instance Distributive FINREL where
  distL @(FR a) @(FR b) @(FR c) = arr (distL @_ @(FS a) @(FS b) @(FS c))
  distR @(FR a) @(FR b) @(FR c) = arr (distR @_ @(FS a) @(FS b) @(FS c))
  distL0 @(FR a) = arr (distL0 @_ @(FS a))
  distR0 @(FR a) = arr (distR0 @_ @(FS a))

instance Closed FINREL where
  type x ~~> y = ExpSA x y
  withObExp @x @y r = withOb2 @_ @x @y r
  curry @x @y = currySA @x @y
  apply @y @z = applySA @y @z
  (^^^) = expSA

instance StarAutonomous FINREL where
  type Dual n = n
  dual = dagger
  dualInv = dagger
  linDist @(FR a) @(FR b) @(FR c) (FinRel m) = withOb2 @_ @(FR b) @(FR c) $ FinRel (P.fmap combines (chunks @a @b m))
  linDistInv @(FR a) @(FR b) @(FR c) (FinRel m) = withOb2 @_ @(FR a) @(FR b) $ FinRel (concatMap @_ @b @_ @a (splits @b @c) m)

instance CompactClosed FINREL where
  distribDual @m @n = dagger (obj @m) `par` dagger (obj @n)
  dualUnit = id

instance MonoidalAction FINREL FINREL where
  type Act p x = p ** x
  withObAct @b @c r = withOb2 @_ @b @c r
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator @b @c @d = associator @_ @b @c @d
  multiplicatorInv @b @c @d = associatorInv @_ @b @c @d

instance Strong FINREL FinRel where
  act = par

instance Costrong FINREL FinRel where
  coact @x = coactCC @x

-- >>> import Data.Type.Nat
-- >>> mappend @(FR Nat3)
-- FinRel {unFinRel = 100 ::: 000 ::: 000 ::: 000 ::: 010 ::: 000 ::: 000 ::: 000 ::: 001 ::: VNil}
instance (SNatI a) => Monoid (FR a) where
  mempty = FinRel (P.maxBound ::: VNil)
  mappend =
    withOb2 @_ @(FR a) @(FR a) $
      FinRel (concatMap @_ @a @_ @a (\i -> P.fmap (\j -> if i P.== j then bit i else 0) universe) universe)

-- >>> import Data.Type.Nat
-- >>> comult @(FR Nat3)
-- FinRel {unFinRel = 100000000 ::: 000010000 ::: 000000001 ::: VNil}
instance (SNatI a) => Comonoid (FR a) where
  counit = arr counit
  comult = arr comult

instance (SNatI a) => Frobenius (FR a) where
  spider @x @y = spiderDefault @x @y @(FR a)
instance Hypergraph FINREL
instance CopyDiscard FINREL

data family Fun :: FINSET +-> FINREL
instance FunctorForRep Fun where
  type Fun @ FS a = FR a
  fmap f = arr f \\ f
instance MonoidalProfunctor (Rep Fun) where
  par0 = Rep par0
  Rep @_ @_ @b l `par` Rep @_ @_ @d r = withOb2 @_ @b @d $ Rep (l `par` r)
instance MonoidalProfunctor (Coprod (Rep Fun)) where
  par0 = Coprod (Rep id)
  Coprod (Rep @_ @_ @b l) `par` Coprod (Rep @_ @_ @d r) = withObCoprod @_ @b @d $ Coprod (Rep (l +++ r))
