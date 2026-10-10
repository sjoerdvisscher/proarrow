{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Tensor networks with integer entries, compared by their entries.
module Props.TensorNetwork (test) where

import Data.Complex (Complex (..))
import Data.Vector.Storable qualified as SV
import GHC.TypeNats (KnownNat)
import Test.Falsify (Property)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (TestOptions (..), testProperty, testPropertyWith)
import Prelude hiding (elem, id, (**), (.))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.TensorNetwork
  ( Scalar
  , TNET (..)
  , TensorNetwork
  , dimsOf
  , entries
  , fromEntries
  , fromVector
  , toVector
  )
import Proarrow.Category.Monoidal.Hypergraph (Sized (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), UN)
import Proarrow.Object (KnownListOf, type (++))
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genNamed
  , genSomeDef
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Proarrow.Tools.Einsum (einsum)
import Props.Mat ()
import Props.SMC (name)

type T2 :: TNET Int
type T2 = TN '[2]

type T3 :: TNET Int
type T3 = TN '[3]

test :: TestTree
test =
  testGroup
    "Tensor networks"
    [ testCategory @(TNET Int)
    , testDagger @(TNET Int)
    , testTerminalObject @(TNET Int)
    , testInitialObject @(TNET Int)
    , testBinaryProducts_ @(TNET Int)
    , testBinaryCoproducts_ @(TNET Int)
    , testDistributive_ @(TNET Int)
    , testTraced_ @(TNET Int)
    , testMonoidal_ @(TNET Int)
    , testSymMonoidal_ @(TNET Int)
    , testClosed_ @(TNET Int)
    , testDialogue_ @(TNET Int)
    , testStarAutonomous_ @(TNET Int)
    , testIsoMix_ @(TNET Int)
    , testCompactClosed_ @(TNET Int)
    , testCopyDiscard_ @(TNET Int)
    , testHypergraph_ @(TNET Int)
    , testGroup
        "entries"
        [ testProperty "fromEntries then entries is the entries (2, 3)" $ do
            f <- genNamed @(T2 ~> T3) "f"
            expect "entries" (entries f) (entries (fromEntries @'[2] @'[3] (entries f)))
        , testProperty "fromVector then toVector is the vector (2, 3)" $ do
            f <- genNamed @(T2 ~> T3) "f"
            expect "entries" (toVector f) (toVector (fromVector @'[2] @'[3] (toVector f)))
        , testProperty "the dagger conjugates complex entries" $
            expect
              "entries"
              (SV.fromList [1 :+ (-2), 3 :+ 4])
              (toVector (dagger (fromVector @'[1] @'[2] (SV.fromList [1 :+ 2, 3 :+ (-4)] :: SV.Vector (Complex Double)))))
        ]
    , testGroup
        "einsum"
        [ testProperty "ij,jk is the name of the composite (2, 3)" $ do
            f <- genNamed @(T2 ~> T3) "f"
            g <- genNamed @(T3 ~> T2) "g"
            expect "entries" (entries (unStr (name (g . f)))) (entries (unStr (einsum @"ij,jk" (name f) (name g))))
        , testProperty "ij,ij,ij-> is the sum of the entrywise product (2, 3)" $ do
            f <- genNamed @(T2 ~> T3) "f"
            g <- genNamed @(T2 ~> T3) "g"
            h <- genNamed @(T2 ~> T3) "h"
            let flat = SV.toList . toVector
            expect
              "entries"
              [[sum (zipWith3 (\x y z -> x * y * z) (flat f) (flat g) (flat h))]]
              (entries (unStr (einsum @"ij,ij,ij->" (name f) (name g) (name h))))
        , testProperty "ij,jk,kl,lm->im is the product of four (3)" (productOfFour @'[3])
        , testPropertyWith fewer "ij,jk,kl,lm->im is the product of four (32)" (productOfFour @'[32])
        , testPropertyWith fewer "kl,jkk,ijx,li->li at Double is the same as at Int (16, 24)" $ do
            v <- genNamed @(TN '[] ~> (TN '[16, 24] :: TNET Int)) "v"
            u <- genNamed @(TN '[] ~> (TN '[24, 16, 16] :: TNET Int)) "u"
            t <- genNamed @(TN '[] ~> (TN '[16, 24, 24] :: TNET Int)) "t"
            w <- genNamed @(TN '[] ~> (TN '[24, 16] :: TNET Int)) "w"
            expect "entries" (asDoubles (ring v u t w)) (entries (ring (double v) (double u) (double t) (double w)))
        ]
    ]
  where
    -- a product of all four would have 32^8 entries; each pairwise contraction costs about 32^3
    fewer = defaultTestOptions{overrideNumTests = Just 5}

-- | The same arrow with its entries as 'Double's, which are contracted with 'gemm' where there is
-- one.
double
  :: (KnownListOf KnownNat as, KnownListOf KnownNat bs)
  => TensorNetwork (TN as :: TNET Int) (TN bs) -> TensorNetwork (TN as :: TNET Double) (TN bs)
double f = fromVector (SV.map fromIntegral (toVector f))

-- | The entries of an arrow as 'Double's.
asDoubles :: TensorNetwork (a :: TNET Int) b -> [[Double]]
asDoubles = fmap (fmap fromIntegral) . entries

-- | The einsum of a chain of four matrices is their product, also at 'Double'.
productOfFour :: forall ns. (KnownListOf KnownNat ns) => Property ()
productOfFour = do
  a <- genNamed @(TN ns ~> (TN ns :: TNET Int)) "a"
  b <- genNamed @(TN ns ~> (TN ns :: TNET Int)) "b"
  c <- genNamed @(TN ns ~> (TN ns :: TNET Int)) "c"
  d <- genNamed @(TN ns ~> (TN ns :: TNET Int)) "d"
  let product4 = unStr (name (d . c . b . a))
  expect "entries" (entries product4) (entries (chain4 a b c d))
  expect "entries at Double" (asDoubles product4) (entries (chain4 (double a) (double b) (double c) (double d)))

-- | The einsum of a chain of four matrices.
chain4
  :: forall e ns
   . (Scalar e, KnownListOf KnownNat ns)
  => TensorNetwork (TN ns :: TNET e) (TN ns)
  -> TensorNetwork (TN ns :: TNET e) (TN ns)
  -> TensorNetwork (TN ns :: TNET e) (TN ns)
  -> TensorNetwork (TN ns :: TNET e) (TN ns)
  -> TensorNetwork (TN '[] :: TNET e) (TN (ns ++ ns))
chain4 a b c d = unStr (einsum @"ij,jk,kl,lm->im" (name a) (name b) (name c) (name d))

-- | The ring of the wiki's einsum page, with the sizes 16 and 24.
ring
  :: (Scalar e)
  => TensorNetwork (TN '[] :: TNET e) (TN '[16, 24])
  -> TensorNetwork (TN '[] :: TNET e) (TN '[24, 16, 16])
  -> TensorNetwork (TN '[] :: TNET e) (TN '[16, 24, 24])
  -> TensorNetwork (TN '[] :: TNET e) (TN '[24, 16])
  -> TensorNetwork (TN '[] :: TNET e) (TN '[24, 16])
ring v u t w =
  unStr
    ( einsum @"kl,jkk,ijx,li->li"
        (Str @'[] @'[TN '[16], TN '[24]] v)
        (Str @'[] @'[TN '[24], TN '[16], TN '[16]] u)
        (Str @'[] @'[TN '[16], TN '[24], TN '[24]] t)
        (Str @'[] @'[TN '[24], TN '[16]] w)
    )

instance Testable (TNET Int) where
  showOb @a = show (dimsOf @(UN TN a))
  genSome = genSomeDef @'[TN '[], TN '[2], TN '[3], TN '[2, 1]]

instance (Ob (a :: TNET Int), Ob b) => TestableType (TensorNetwork a b) where
  gen = GenNonEmpty (fromVector <$> SV.replicateM (sizeOf @_ @a * sizeOf @_ @b) (liftA2 (*) (elem [1, -1]) (elem [0 .. 9])))

instance (Ob (a :: TNET Int), Ob b) => TestingEqShow (TensorNetwork a b) where
  eqP l r = pure (toVector l == toVector r)
  showP = show . entries

instance TestableProfunctor (TensorNetwork :: CAT (TNET Int))
