{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Simulator (test) where

import Test.Tasty (TestTree, testGroup)
import Prelude

import Proarrow.Category.Instance.Simulator
import Proarrow.Core (CategoryOf (..), UN)
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genNamed
  , genSomeDef
  )
import Proarrow.Testing.Laws (testCategory, testCopyDiscard, testMonoidal, testSymMonoidal)
import Props.Hask ()

test :: TestTree
test =
  testGroup
    "Simulator"
    [ testCategory @SIMULATOR
    , testMonoidal @SIMULATOR (\r -> r)
    , testSymMonoidal @SIMULATOR (\r -> r)
    , testCopyDiscard @SIMULATOR (\r -> r)
    ]

instance Testable SIMULATOR where
  type TestOb a = (Ob a, TestOb (UN Sim a))
  obFromTestOb r = r
  showOb @(Sim a) = showOb @_ @a
  genSome = genSomeDef @'[Sim Bool, Sim (), Sim (Bool, Bool)]

instance (TestOb (Sim a), TestOb (Sim b)) => TestableType (Simulator (Sim a) (Sim b)) where
  gen = fromTransition <$> gen @((Bool, a) -> (b, Bool))
    where
      fromTransition transition = go False
        where
          go state = Simulator \x -> let (y, state') = transition (state, x) in (y, go state')

instance (TestOb (Sim a), TestOb (Sim b)) => TestingEqShow (Simulator (Sim a) (Sim b)) where
  showP _ = "<state machine>"
  eqP f g = do
    xs <- genNamed @[a] "clock inputs"
    eqP (runSimulator f xs) (runSimulator g xs)

instance TestableProfunctor Simulator
