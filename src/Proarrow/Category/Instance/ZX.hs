{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.ZX where

import Data.Bits (Bits (..), shiftL, (.|.))
import Data.Char (chr)
import Data.Complex (Complex (..), conjugate, magnitude, mkPolar)
import Data.List (intercalate, sort)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import GHC.TypeLits.Witnesses ((%+))
import GHC.TypeNats (KnownNat, Nat, natVal, pattern SNat, type (+))
import Numeric (showFFloat)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (id, (.))

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Object.Dual (CompactClosed (..), ExpSA, StarAutonomous (..), currySA, expSA, uncurrySA)
import Proarrow.Object.Exponential (Closed (..))

newtype Bitstring (n :: Nat) = BS Int
  deriving (Eq, Ord, Num)

instance (KnownNat n) => Bounded (Bitstring n) where
  minBound = BS 0
  maxBound = BS ((1 `shiftL` nat @n) - 1)
instance Enum (Bitstring n) where
  fromEnum (BS x) = x
  toEnum x = BS x

-- | Split n + m bits into two parts: the lower n bits and the higher m bits.
split :: (KnownNat n) => Bitstring (n + m) -> (Bitstring n, Bitstring m)
split @n (BS x) = case (x `divMod` (1 `shiftL` nat @n)) of (m, n) -> (BS n, BS m)

-- | Combine two bitstrings of lengths n and m into one bitstring with the n lower bits or m higher bits.
combine :: (KnownNat n) => Bitstring n -> Bitstring m -> Bitstring (n + m)
combine @n (BS x) (BS y) = BS ((y `shiftL` nat @n) .|. x)

-- The order is (output, input)!
type SparseMatrix o i = Map.Map (Bitstring o, Bitstring i) (Complex Double)

epsilon :: Double
epsilon = 1e-12

filterSparse :: SparseMatrix o i -> SparseMatrix o i
filterSparse = Map.filter (\z -> epsilon < magnitude z)

transpose :: SparseMatrix o i -> SparseMatrix i o
transpose = Map.mapKeys \(o, i) -> (i, o)

mirror :: (KnownNat n) => Bitstring n -> Bitstring (n + n)
mirror @n (BS x) = BS (go (nat @n) x x)
  where
    go 0 _ acc = acc
    go k y acc = go (k - 1) (y `shiftR` 1) ((acc `shiftL` 1) .|. (y .&. 1))

enumAll :: (KnownNat n) => [Bitstring n]
enumAll = [minBound .. maxBound]

nat :: (KnownNat n) => Int
nat @n = fromIntegral $ natVal (Proxy :: Proxy n)

type ZX :: CAT Nat
data ZX i o where
  ZX :: (KnownNat i, KnownNat o) => SparseMatrix o i -> ZX i o

instance (KnownNat n) => Show (Bitstring n) where
  show (BS x) = go (nat @n) x ""
    where
      go 0 _ acc = acc
      go n bs acc = case bs `divMod` 2 of (r, b) -> go (n - 1) r (chr (48 + b) : acc)

instance Show (ZX a b) where
  show (ZX m) = intercalate ", " (sort (fmt <$> Map.toList m))
    where
      fmt ((o, i), r :+ c) =
        show i
          ++ "->"
          ++ show o
          ++ "="
          ++ (if abs (1 - r) < epsilon then "1" else showFFloat (Just 3) r "")
          ++ (if abs c < epsilon then "" else " :+ " ++ showFFloat (Just 3) c "")

instance Profunctor ZX where
  dimap = dimapDefault
  r \\ ZX _ = r
instance Promonad ZX where
  id @n = ZX $ Map.fromList [((i, i), 1) | i <- enumAll @n]
  ZX n . ZX m =
    ZX $
      filterSparse $
        Map.fromListWith
          (+)
          [ ((c, a), mv * nv)
          | ((c, b1), mv) <- Map.toList n
          , ((b2, a), nv) <- Map.toList m
          , b1 == b2
          ]
-- | The category of qubits, to implement ZX calculus from quantum computing.
instance CategoryOf Nat where
  type (~>) = ZX
  type Ob a = KnownNat a

instance DaggerProfunctor ZX where
  dagger (ZX m) = ZX $ Map.fromList [((i, o), conjugate v) | ((o, i), v) <- Map.toList m]

instance MonoidalProfunctor ZX where
  par0 = ZX Map.empty
  ZX @ni @no n `par` ZX @mi @mo m =
    withOb2 @_ @ni @mi $
      withOb2 @_ @no @mo $
        ZX $
          Map.fromList
            [ ((combine no mo, combine ni mi), nv * mv)
            | ((no, ni), nv) <- Map.toList n
            , ((mo, mi), mv) <- Map.toList m
            ]
instance Monoidal Nat where
  type Unit = 0
  type p ** q = p + q
  withOb2 @a @b r = case (SNat @a) %+ (SNat @b) of SNat -> r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @a @b @c = withOb2 @_ @a @b $ withOb2 @_ @(a + b) @c $ unsafeCoerce (obj @(a + b + c))
  associatorInv @a @b @c = withOb2 @_ @a @b $ withOb2 @_ @(a + b) @c $ unsafeCoerce (obj @(a + b + c))
instance SymMonoidal Nat where
  swap @m @n =
    withOb2 @_ @m @n $
      withOb2 @_ @n @m $
        ZX $
          Map.fromList
            [ ((combine n m, combine m n), 1)
            | n <- enumAll @n
            , m <- enumAll @m
            ]

instance Closed Nat where
  type x ~~> y = ExpSA x y
  withObExp @a @b r = withOb2 @_ @a @b r
  curry @x @y = currySA @x @y
  uncurry @y @z = uncurrySA @_ @y @z
  (^^^) = expSA

instance StarAutonomous Nat where
  type Dual x = x
  dual (ZX m) = ZX (transpose m)
  dualInv = dual
  linDist @_ @b @c (ZX m) =
    withOb2 @_ @b @c $
      ZX (Map.mapKeys (\(c, ab) -> case split ab of (a, b) -> (combine b c, a)) m)
  linDistInv @a @b (ZX m) =
    withOb2 @_ @a @b $
      ZX (Map.mapKeys (\(bc, a) -> case split bc of (b, c) -> (c, combine a b)) m)

instance CompactClosed Nat where
  distribDual @a @b = withOb2 @_ @a @b id
  dualUnit = ZX Map.empty

zSpider :: (KnownNat i, KnownNat o) => Double -> ZX i o
zSpider alpha = ZX $ Map.fromList $ [(minBound, 1), (maxBound, mkPolar 1 alpha)]

xSpider :: (KnownNat i, KnownNat o) => Double -> ZX i o
xSpider alpha = hadamard . zSpider alpha . hadamard

cup :: (KnownNat n) => ZX 0 (n + n)
cup @n = withOb2 @_ @n @n $ ZX $ Map.fromList [((mirror i, 0), 1) | i <- enumAll @n]

cap :: (KnownNat n) => ZX (n + n) 0
cap @n = withOb2 @_ @n @n $ ZX $ Map.fromList [((0, mirror i), 1) | i <- enumAll @n]

zCopy :: ZX 1 2
zCopy = zSpider 0

zDisc :: ZX 1 0
zDisc = zSpider 0

xCopy :: ZX 1 2
xCopy = xSpider 0

xDisc :: ZX 1 0
xDisc = xSpider 0

zeroState :: ZX 0 1
zeroState = xSpider 0

oneState :: ZX 0 1
oneState = xSpider pi

plusState :: ZX 0 1
plusState = zSpider 0

minusState :: ZX 0 1
minusState = zSpider pi

not :: ZX 1 1
not = xSpider pi

-- | Controlled NOT gate
cnot :: ZX 2 2
cnot = (id `par` xSpider @2 0) . (zCopy `par` id)

-- | Greenberger–Horne–Zeilinger state
ghzState :: ZX 0 3
ghzState = zSpider 0

hadamard :: (KnownNat n) => ZX n n
hadamard @n = ZX $ Map.fromList [((i, j), (sign i j * amp) :+ 0) | i <- enumAll @n, j <- enumAll @n]
  where
    amp = 1 / sqrt (fromIntegral (shiftL (1 :: Int) (nat @n)))
    sign (BS a) (BS b) = if even (popCount (a .&. b)) then 1 else -1