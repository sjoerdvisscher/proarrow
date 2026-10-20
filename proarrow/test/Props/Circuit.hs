{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Circuit (test) where

import Data.Kind (Constraint)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (fmap, id, (**), (.))

import Proarrow.Category.Instance.Circuit
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Tensor)
import Proarrow.Category.Monoidal.Strength (Costrong (..))
import Proarrow.Core (Is, Promonad (..), UN, obj)
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Profunctor.Representable (Rep)
import Proarrow.Testing
  ( GenTotal
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genNamed
  , genSomeDef
  , oneOfTotal
  , optGen
  )
import Proarrow.Testing.Laws
  ( testCategory
  , testCopyDiscard
  , testMonoidal
  , testMonoidalProfunctor
  , testProfunctor
  , testRepresentable
  , testSymMonoidal
  , testTraced
  )
import Props.Hask ()
import Props.Simulator ()

test :: TestTree
test =
  testGroup
    "Circuit"
    [ testCategory @Wires
    , testMonoidal @Wires (\r -> r)
    , testSymMonoidal @Wires (\r -> r)
    , testCopyDiscard @Wires (\r -> r)
    , testTraced @Wires (\r -> r)
    , testGroup
        "Prepared"
        [ testCategory @PREPARED
        , testMonoidal @PREPARED (\r -> r)
        , testSymMonoidal @PREPARED (\r -> r)
        , testCopyDiscard @PREPARED (\r -> r)
        ]
    , testGroup
        "Value"
        [ testProfunctor @(Rep Value)
        , testRepresentable @(Rep Value) (\r -> r)
        , testMonoidalProfunctor @(Rep Value) (\r -> r) (\r -> r)
        ]
    ]

-- Generate circuits through the public API, preserving the grouping of their boundaries.
type TestWires :: Wires -> Constraint
class (KnownWires a, TestOb (Sample a)) => TestWires a where
  wireName :: String
  projections :: [Circuit a Bit]
  assemble :: (KnownWires b) => GenTotal (Circuit b Bit) -> GenTotal (Circuit b a)
instance TestWires Bit where
  wireName = "Bit"
  projections = [id]
  assemble = id
instance TestWires Empty where
  wireName = "Empty"
  projections = []
  assemble _ = pure counit
instance (TestWires a, TestWires b) => TestWires (Pair a b) where
  wireName = "(" ++ wireName @a ++ " ** " ++ wireName @b ++ ")"
  projections =
    map (. (rightUnitor . (obj @a ** counit @b))) (projections @a)
      ++ map (. (leftUnitor . (counit @a ** obj @b))) (projections @b)
  assemble bit = (\f g -> (f ** g) . comult) <$> assemble @a bit <*> assemble @b bit

instance Testable Wires where
  type TestOb a = TestWires a
  obFromTestOb r = r
  showOb @a = wireName @a
  genSome = genSomeDef @'[Empty, Bit, Pair Bit Bit]

genBit :: forall a. (TestWires a) => Int -> GenTotal (Circuit a Bit)
genBit depth = oneOfTotal (leaves ++ gates)
  where
    leaves = ((\b -> constant b . counit) <$> gen @Bool) : map pure (projections @a)
    child = genBit @a (depth - 1)
    gates
      | depth <= 0 = []
      | otherwise =
          [ (notGate .) <$> child
          , (\gate f g -> gate . (f ** g) . comult) <$> optGen [andGate, orGate, xorGate] <*> child <*> child
          , (\s f g -> mux . ((s ** f) ** g) . (comult ** id) . comult) <$> child <*> child <*> child
          , (\initial f -> register initial . f) <$> gen @Bool <*> child
          , (\initial f -> coact @Tensor @Circuit @Bit (comult . register initial . xorGate . (obj @Bit ** f)))
              <$> gen @Bool
              <*> child
          ]

instance (TestWires a, TestWires b) => TestableType (Circuit a b) where
  gen = assemble @b (genBit @a 2)

instance (TestWires a, TestWires b) => TestingEqShow (Circuit a b) where
  showP = renderNetlist . netlist
  eqP f g = do
    xs <- genNamed @[Sample a] "clock inputs"
    -- Trace laws can create unguarded cycles. Compare their rejection status rather than local
    -- wire numbers; executable circuits are compared by their outputs over the sampled clocks.
    case (simulate f xs, simulate g xs) of
      (Right ys, Right zs) -> eqP ys zs
      (Left _, Left _) -> pure True
      _ -> pure False

instance TestableProfunctor Circuit

instance Testable PREPARED where
  type TestOb a = (Is Ready a, TestWires (UN Ready a))
  obFromTestOb r = r
  showOb @(Ready a) = "Ready " ++ wireName @a
  genSome = genSomeDef @'[Ready Empty, Ready Bit, Ready (Pair Bit Bit)]

instance (TestWires a, TestWires b) => TestableType (Prepared (Ready a) (Ready b)) where
  -- Generated circuits contain only guarded feedback; rejection is a generator bug.
  gen = either (error . show) id . prepare . netlist <$> gen @(Circuit a b)

instance (TestWires a, TestWires b) => TestingEqShow (Prepared (Ready a) (Ready b)) where
  showP = showP . fmap @Value
  eqP f g = eqP (fmap @Value f) (fmap @Value g)

instance TestableProfunctor Prepared
instance TestableProfunctor (Rep Value)
