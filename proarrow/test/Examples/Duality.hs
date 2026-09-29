-- | Duals in "Proarrow.Tools.SMC", over 'FinRel', which is compact closed and also traced: the
-- snake equations, and the trace built from the duality agreeing with 'FinRel''s own.
module Examples.Duality (test) where

import Control.Monad (unless)
import Data.Type.Nat (Nat (..))
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.FinRel (FINREL (..))
import Proarrow.Category.Instance.IntConstruction (INT (..), IntConstruction (..))
import Proarrow.Category.Monoidal (type (**))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..), combineDual)
import Proarrow.Category.Monoidal.Strength (trace)
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Testing (genNamed)
import Proarrow.Tools.SMC (combineDualT, loopCC, snakeT)
import Props.FinRel ()

type F1 = FR (S Z)
type F2 = FR (S (S Z))
type F3 = FR (S (S (S Z)))

check :: String -> Bool -> Property ()
check msg ok = unless ok (testFailed msg)

test :: TestTree
test =
  testGroup
    "Duality (Proarrow.Tools.SMC)"
    [ testProperty "snake is the identity (FinRel 2)" $ check "differs from id" (snakeT @F2 == id)
    , testProperty "snake is the identity (FinRel 3)" $ check "differs from id" (snakeT @F3 == id)
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
