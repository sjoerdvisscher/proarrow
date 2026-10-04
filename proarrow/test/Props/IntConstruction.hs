{-# OPTIONS_GHC -Wno-orphans #-}

-- | The Int construction over 'FinRel', whose trace is a finite existential, so composing
-- generated morphisms always terminates (unlike in Hask, where the trace is a lazy fixed point).
module Props.IntConstruction where

import Data.Type.Nat (Nat (..))
import Test.Tasty (TestTree, testGroup)
import Prelude (($), (++))

import Proarrow.Category.Instance.FinRel (FINREL (..), FinRel)
import Proarrow.Category.Instance.IntConstruction (INT (..), IntConstruction (..), IntMinus, IntPlus)
import Proarrow.Category.Monoidal (Monoidal (..), type (**))
import Proarrow.Core (CAT, CategoryOf (..), (\\))

import Proarrow.Testing (Testable (..), TestableProfunctor, TestableType (..), TestingEqShow (..), genSomeDef, invmap)
import Proarrow.Testing.Laws
import Props.FinRel ()

test :: TestTree
test =
  testGroup
    "IntConstruction"
    [ testCategory @(INT FINREL)
    , testMonoidal_ @(INT FINREL)
    , testSymMonoidal_ @(INT FINREL)
    , testClosed_ @(INT FINREL)
    , testDialogue_ @(INT FINREL)
    , testStarAutonomous_ @(INT FINREL)
    , testIsoMix_ @(INT FINREL)
    , testCompactClosed_ @(INT FINREL)
    ]

type F0 = FR Z
type F1 = FR (S Z)
type F2 = FR (S (S Z))

instance Testable (INT FINREL) where
  showOb @(I p m) = "I " ++ showOb @FINREL @p ++ " " ++ showOb @FINREL @m
  genSome = genSomeDef @'[I F1 F0, I F0 F1, I F1 F1, I F2 F1]
  genSomeSmall = genSomeDef @'[I F1 F0, I F0 F1, I F1 F1]

-- | The underlying morphism of the base category.
unInt :: IntConstruction a b -> IntPlus a ** IntMinus b ~> IntMinus a ** IntPlus b
unInt (Int f) = f

instance (Ob a, Ob b) => TestableType (IntConstruction (a :: INT FINREL) b) where
  gen =
    withOb2 @FINREL @(IntPlus a) @(IntMinus b) $
      withOb2 @FINREL @(IntMinus a) @(IntPlus b) $
        invmap Int unInt (gen @(FinRel (IntPlus a ** IntMinus b) (IntMinus a ** IntPlus b)))
instance (Ob a, Ob b) => TestingEqShow (IntConstruction (a :: INT FINREL) b) where
  eqP (Int l) (Int r) = eqP l r \\ l
  showP (Int f) = showP f \\ f
instance TestableProfunctor (IntConstruction :: CAT (INT FINREL))
