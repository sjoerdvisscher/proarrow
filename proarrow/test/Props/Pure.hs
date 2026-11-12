{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Pure (test) where

import Data.Kind (Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.Bool (Booleans)
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.OpenHypergraph (SIMPLIFY, Wires, copyDiscard, prim1, simplify)
import Proarrow.Category.Monoidal (MonoidalProfunctor (..), SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Strictified (unStr)
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), obj)
import Proarrow.Functor qualified as F
import Proarrow.Profunctor.Instance.Coyoneda (Coyoneda (..))
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Promonad.Pure
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestableTypeP
  , TestingEqShow (..)
  , check
  , expect
  , genNamed
  , oneOfTotal
  , testEq
  , withTestOb2Def
  )
import Proarrow.Testing.Laws
import Props.Bool ()
import Props.Hask ()
import Props.Kleisli ()

instance (Testable k, Promonad p, TestableTypeP p, TestOb a, TestOb b) => TestableType (WithPure (p :: CAT k) a b) where
  gen =
    oneOfTotal
      [ Pure <$> gen @(a ~> b)
      , liftWithPure <$> gen @(p a b)
      , (\f g p -> Effect (Coyoneda f g p)) <$> gen @(a ~> a) <*> gen @(b ~> b) <*> gen @(p a b)
      ]

instance (Promonad p, TestingEqShow (p a b)) => TestingEqShow (WithPure p a b) where
  eqP l r = eqP (lowerWithPure l) (lowerWithPure r)
  showP (Pure f) = "Pure (" ++ showP (lowerWithPure (Pure f) :: p a b) ++ ")"
  showP p = "Effect (" ++ showP (lowerWithPure p) ++ ")"

instance (Promonad p, TestableProfunctor p, TestableTypeP p) => TestableProfunctor (WithPure p)

type Optional :: CAT Type
type Optional = Star (F.Prelude Maybe)
type Ordered :: CAT Type
type Ordered = Star (F.Prelude ((,) [Bool]))
type Routed = KLEISLI (WithPure Optional)

swapWires :: Wires '[KL Bool, KL Bool] ~> (Wires '[KL Bool, KL Bool] :: SIMPLIFY Routed)
swapWires = swap @(SIMPLIFY Routed) @(Wires '[KL Bool]) @(Wires '[KL Bool])

test :: TestTree
test =
  testGroup
    "Pure"
    [ testGroup
        "Maybe"
        [ testProfunctor @(WithPure Optional)
        , testPromonad @(WithPure Optional)
        , testMonoidalProfunctor @(WithPure Optional) (\r -> r) (\r -> r)
        , testMonStrong @(WithPure Optional) (\r -> r)
        , testCategory @Routed
        , testMonoidal @Routed (\r -> r)
        , testSymMonoidal @Routed (\r -> r)
        , testCopyDiscard @Routed (\r -> r)
        ]
    , testGroup
        "Ordered writer"
        [ testProfunctor @(WithPure Ordered)
        , testPromonad @(WithPure Ordered)
        , testMonoidalProfunctor @(WithPure Ordered) (\r -> r) (\r -> r)
        , testMonStrong @(WithPure Ordered) (\r -> r)
        , testProperty "lowering preserves composition" $ do
            p <- genNamed @(WithPure Ordered Bool Bool) "p"
            q <- genNamed @(WithPure Ordered Bool Bool) "q"
            testEq "lowering" "lower (q . p)" (lowerWithPure (q . p)) "lower q . lower p" (lowerWithPure q . lowerWithPure p)
        , testProperty "lowering preserves composition of carried effects" $ do
            p <- genNamed @(WithPure Ordered Bool Bool) "p"
            q <- genNamed @(WithPure Ordered Bool Bool) "q"
            let carriedP = act @Tensor @_ @Bool p
                carriedQ = act @Tensor @_ @Bool q
            testEq "lowering" "lower (q . p)" (lowerWithPure (carriedQ . carriedP)) "lower q . lower p" (lowerWithPure carriedQ . lowerWithPure carriedP)
        , testProperty "lowering preserves tensor" $ do
            p <- genNamed @(WithPure Ordered Bool Bool) "p"
            q <- genNamed @(WithPure Ordered Bool Bool) "q"
            testEq "lowering" "lower (p ** q)" (lowerWithPure (p ** q)) "lower p ** lower q" (lowerWithPure p ** lowerWithPure q)
        ]
    , testGroup
        "Boolean base category"
        [ testProfunctor @(WithPure Booleans)
        , testPromonad @(WithPure Booleans)
        , testMonoidalProfunctor @(WithPure Booleans) (\ @a @b -> withTestOb2Def @a @b) (\ @a @b -> withTestOb2Def @a @b)
        ]
    , testProperty "structural read-back stays pure" $ do
        let graph :: Wires '[KL Bool] ~> (Wires '[KL Bool, KL Bool] :: SIMPLIFY Routed)
            graph = swapWires . copy
        case simplify copyDiscard graph of
          Left err -> error err
          Right arrow -> case unStr arrow of
            Kleisli (Pure f) -> expect "copy and swap" (True, True) (f True)
            _ -> check "structural routing introduced an effect" False
    , testProperty "read-back of an effect and carried wires agrees with direct execution" $ do
        let effect :: Kleisli (KL Bool :: Routed) (KL Bool)
            effect = Kleisli (liftWithPure (Star (\x -> F.Prelude (if x then Nothing else Just True))))
            graph :: Wires '[KL Bool, KL Bool] ~> (Wires '[KL Bool, KL Bool] :: SIMPLIFY Routed)
            graph = swapWires . (prim1 effect ** obj @(Wires '[KL Bool])) . swapWires
        case simplify copyDiscard graph of
          Left err -> error err
          Right arrow -> case unStr arrow of
            Kleisli p -> case lowerWithPure p of
              Star f -> do
                expect "successful branch" (Just (True, True)) (F.unPrelude (f (True, False)))
                expect "failed branch" Nothing (F.unPrelude (f (False, True)))
    ]
