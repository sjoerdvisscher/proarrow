{-# LANGUAGE QualifiedDo #-}

-- | Index notation in "Proarrow.Tools.SMC", checked against the structure of the category: in
-- 'FinRel', where a sum over an index is "there is", and in 'Mat' over 'Int', where it is a sum of
-- numbers.
module Props.SMC (test) where

import Data.Type.Nat (Nat (..), Nat2, Nat3)
import Data.Vec.Lazy (Vec (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, mappend, mempty, (**), (.))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.FinRel (FINREL (..))
import Proarrow.Category.Instance.Mat (Mat (..), MatK (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Hypergraph (cap, cup)
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Testing (check, genNamed)
import Proarrow.Tools.SMC (SYN (..), delta, lift, sumOver, toSMC, unit, (*^))
import Proarrow.Tools.SMC qualified as SMC
import Proarrow.Tools.SMC.Examples (hadamardT, matMulT, traceIdxT)
import Props.FinRel ()
import Props.Mat ()

type F2 = FR (S (S Z))
type F3 = FR (S (S (S Z)))
type F4 = FR (S (S (S (S Z))))

type M2 = M Nat2 :: MatK Int
type M3 = M Nat3 :: MatK Int

-- | The transpose in index notation: the entry at @j@ and @i@ is the entry of @f@ at @i@ and @j@.
transposeT :: Mat M2 M3 -> Mat M3 M2
transposeT f = toSMC @(F M3) \j -> sumOver @(F M2) \i -> delta (lift f i) j *^ i

-- `\_ -> unit` binds a summed index that is not used, which is what is tested.
{- HLINT ignore test "Use const" -}
test :: TestTree
test =
  testGroup
    "SMC"
    [ testGroup
        "FinRel"
        [ testProperty "matrix multiplication is composition (2, 3, 4)" $ do
            f <- genNamed @(F2 ~> F3) "f"
            g <- genNamed @(F3 ~> F4) "g"
            check "differs from g . f" (matMulT f g == g . f)
        , testProperty "the trace is the cap after the cup (3)" $ do
            f <- genNamed @(F3 ~> F3) "f"
            check "differs" (traceIdxT f == cap @F3 . (f ** obj @F3) . cup @F3)
        , testProperty "the entrywise product is mappend after the two after comult (2, 3)" $ do
            f <- genNamed @(F2 ~> F3) "f"
            g <- genNamed @(F2 ~> F3) "g"
            check "differs" (hadamardT f g == mappend @F3 . (f ** g) . comult @F2)
        , testProperty "an index used twice from a sum is the cup (3)" $
            check "differs from cup" (toSMC @I (\() -> sumOver @(F F3) \j -> j SMC.** j) == cup @F3)
        , testProperty "an unused summed index is the counit after the unit (3)" $
            check "differs" (toSMC @I (\() -> sumOver @(F F3) \_ -> unit) == counit @F3 . mempty @F3)
        ]
    , testGroup
        "Mat Int"
        [ testProperty "matrix multiplication is composition (2, 3, 2)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            g <- genNamed @(M3 ~> M2) "g"
            check "differs from g . f" (unMat (matMulT f g) == unMat (g . f))
        , testProperty "the trace is the sum of the diagonal (3)" $ do
            f <- genNamed @(M3 ~> M3) "f"
            check "differs from cap . (f ** id) . cup" (unMat (traceIdxT f) == unMat (cap @M3 . (f ** obj @M3) . cup @M3))
        , testProperty "the trace of the identity is the dimension (3)" $
            check "not 3" (unMat (traceIdxT (obj @M3)) == ((3 ::: VNil) ::: VNil))
        , testProperty "the transpose is the dagger (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            check "differs from dagger" (unMat (transposeT f) == unMat (dagger f))
        , testProperty "the entrywise product is mappend after the two after comult (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            g <- genNamed @(M2 ~> M3) "g"
            check "differs" (unMat (hadamardT f g) == unMat (mappend @M3 . (f ** g) . comult @M2))
        ]
    ]
