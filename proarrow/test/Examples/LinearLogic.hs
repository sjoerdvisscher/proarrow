{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | The linear logic connectives of "Proarrow.Tools.SMC", each tested where it lives.
--
-- * Duals over 'FinRel', which is compact closed and also traced: the snake equations,
--   'combineDual', and the trace built from the duality agreeing with 'FinRel''s own.
-- * Classical reasoning in the Kleisli category of the continuation monad, which is
--   *-autonomous but not compact closed: its dual is @a -> r@, so terms can be run on values and
--   continuations. And 'annihilate' in 'LINEAR', which is isomix but not compact closed.
-- * The additives over 'FinRel', which is distributive: case analysis agrees with the
--   distributor, and 'with' with the pairing.
module Examples.LinearLogic (test, snakePicture) where

import Data.List (isInfixOf)
import Data.Type.Nat (Nat (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (fst, id, snd, (**), (.))

import Proarrow.Category.Instance.FinRel (FINREL (..))
import Proarrow.Category.Instance.IntConstruction (INT (..), IntConstruction (..))
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.Linear (LINEAR (..), Linear (..))
import Proarrow.Category.Monoidal (SymMonoidal (..), type (**))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..), combineDual)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Monoidal.IsoMix (IsoMix)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strength (trace)
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Promonad.Cont (Cont (..))
import Proarrow.Testing (check, genNamed)
import Proarrow.Tools.Diagrams.Svg qualified as Svg
import Proarrow.Tools.SMC
  ( SYN (D, F, (:**))
  , annihilate
  , bothWaysT
  , combineDualT
  , contraT
  , distT
  , dneT
  , dniT
  , loopCC
  , snakeDualT
  , snakeT
  , swapEitherT
  , toSMC
  )
import Proarrow.Tools.SMC qualified as SMC
import Props.FinRel ()

test :: TestTree
test = testGroup "Linear logic (Proarrow.Tools.SMC)" [duality, classical, additives]

type F1 = FR (S Z)
type F2 = FR (S (S Z))
type F3 = FR (S (S (S Z)))

-- * Duals

-- | The snake on the dual as a string diagram: a cup and a cap.
snakePicture :: String
snakePicture = Svg.render (snakeDualT @(Svg.S '[Svg.Wire "a"]))

duality :: TestTree
duality =
  testGroup
    "Duality"
    [ testProperty "snake is the identity (FinRel 2)" $ check "differs from id" (snakeT @F2 == id)
    , testProperty "snake is the identity (FinRel 3)" $ check "differs from id" (snakeT @F3 == id)
    , testProperty "the snake on the dual is the identity (FinRel 2)" $ check "differs from id" (snakeDualT @F2 == id)
    , testProperty "the snake draws" $ check "not an SVG document" ("<svg" `isInfixOf` snakePicture)
    , testProperty "combineDual (FinRel 2, 3)" $
        check "differs from combineDual" (combineDualT @F2 @F3 == combineDual @F2 @F3)
    , -- the Int construction's duals swap the two halves; bigger objects than these get expensive
      testProperty "combineDual (Int construction over FinRel)" $
        check "differs from combineDual" $
          case (combineDualT @(I F1 F2) @(I F1 F1), combineDual @(I F1 F2) @(I F1 F1)) of
            (Int f, Int g) -> f == g
    , testProperty "combineDual inverts distribDual (FinRel 3, 2)" $
        check "not inverses" (combineDualT @F3 @F2 . distribDual @_ @F3 @F2 == id)
    , testProperty "the trace from the duality is FinRel's trace" $ do
        h <- genNamed @(F2 ** F2 ~> F3 ** F2) "h"
        check "differs from trace" (loopCC @F2 @F3 @F2 h == trace @(~>) @F2 @F2 @F3 h)
    , testProperty "the trace from the duality is FinRel's trace (other sizes)" $ do
        h <- genNamed @(F3 ** F1 ~> F2 ** F1) "h"
        check "differs from trace" (loopCC @F3 @F2 @F1 h == trace @(~>) @F1 @F3 @F2 h)
    ]

-- * Classical reasoning

type K = KLEISLI (Cont Int)

-- | Run a morphism of @K@ on a value and a continuation.
run :: (KL a :: K) ~> KL b -> a -> (b -> Int) -> Int
run (Kleisli (Cont m)) a k = m k a

incr :: (KL Int :: K) ~> KL Int
incr = Kleisli (Cont \k a -> k (a + 1) * 2)

-- Values, continuations, and elements and continuations of the dual and double dual of @Int@.
xs :: [Int]
xs = [0, 3, 7]

ks :: [Int -> Int]
ks = [(* 2), (+ 1)]

nns :: [(Int -> Int) -> Int]
nns = [\c -> c 3 + c 4, ($ 5)]

nnks :: [((Int -> Int) -> Int) -> Int]
nnks = [\nn -> nn (* 3), \nn -> nn id + 1]

nbs :: [Int -> Int]
nbs = [(* 5), subtract 1]

nks :: [(Int -> Int) -> Int]
nks = [($ 2), \g -> g 0 + g 9]

-- | Use a refutation of @a@ on an @a@ and keep the @b@: needs only isomix.
annihilateT :: forall {k} (a :: k) b. (IsoMix k, SymMonoidal k, Ob a, Ob b) => Dual a ** a ** b ~> b
annihilateT = toSMC @(D (F a) :** F a :** F b) \p -> SMC.do
  ((na, a), b) <- p
  () <- annihilate na a
  b

runL :: (L a :: LINEAR) ~> L b -> a -> b
runL (Linear g) a = g a

classical :: TestTree
classical =
  testGroup
    "Classical"
    [ testProperty "double negation elimination after introduction is the identity" $
        check "differs" (and [run (dneT @(KL Int) . dniT) x k == k x | x <- xs, k <- ks])
    , testProperty "double negation introduction is doubleNegInv" $
        check "differs" (and [run (dniT @(KL Int)) x k == run (doubleNegInv @K @(KL Int)) x k | x <- xs, k <- nnks])
    , testProperty "double negation elimination is doubleNeg" $
        check "differs" (and [run (dneT @(KL Int)) nn k == run (doubleNeg @K @(KL Int)) nn k | nn <- nns, k <- ks])
    , testProperty "annihilate in LINEAR" $
        check "differs" (and [runL (annihilateT @(L ()) @(L Bool)) ((\() -> (), ()), b) == b | b <- [False, True]])
    , testProperty "contraposition is dual" $
        check "differs" (and [run (contraT incr) nb k == run (dual incr) nb k | nb <- nbs, k <- nks])
    ]

-- * Additives

additives :: TestTree
additives =
  testGroup
    "Additives"
    [ testProperty "case analysis is the distributor (FinRel 2, 1, 3)" $
        check "differs from distL" (distT @F2 @F1 @F3 == distL @_ @F2 @F1 @F3)
    , testProperty "swapping a coproduct twice is the identity (FinRel 2, 3)" $
        check "differs from id" (swapEitherT @F3 @F2 . swapEitherT @F2 @F3 == id)
    , testProperty "the projections of a pair both ways are id and swap (FinRel 2, 3)" $ do
        check "fst differs from id" (fst @_ @(F2 ** F3) @(F3 ** F2) . bothWaysT @F2 @F3 == id)
        check "snd differs from swap" (snd @_ @(F2 ** F3) @(F3 ** F2) . bothWaysT @F2 @F3 == swap @_ @F2 @F3)
    ]
