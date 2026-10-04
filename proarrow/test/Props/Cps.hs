{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Cps where

import Data.Kind (Type)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (id, (.))

import Proarrow.Category.Instance.Cps (CPS (..), Cps (..))
import Proarrow.Core (CAT, CategoryOf (..), UN)
import Proarrow.Testing
  ( SomeProfunctorElt (..)
  , Testable (..)
  , TestableProfunctor (..)
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , invmap
  )
import Proarrow.Testing.Laws
import Props.Hask ()

-- | The dialogue category of 'Type' with answer object 'Bool', whose dual is @a -> Bool@, and the
-- isomix one with answer object @()@, whose dual @a -> ()@ is a point.
test :: TestTree
test =
  testGroup
    "CPS"
    [ testGroup
        "answer Bool"
        [ testCategory @(CPS Bool)
        , testMonoidal @(CPS Bool) (\r -> r)
        , testSymMonoidal @(CPS Bool) (\r -> r)
        , testClosed @(CPS Bool) (\r -> r) (\r -> r)
        , testDialogue @(CPS Bool) (\r -> r) (\r -> r)
        ]
    , -- the dialogue laws are the same instance as at Bool; only the isomix structure is new
      testGroup "answer ()" [testIsoMix @(CPS ()) (\r -> r) (\r -> r)]
    ]

instance (TestOb a, TestOb b) => TestableType (Cps (C a :: CPS (r :: Type)) (C b)) where
  gen = invmap Cps unCps (gen @(a -> b))
instance (TestOb a, TestOb b) => TestingEqShow (Cps (C a :: CPS (r :: Type)) (C b)) where
  eqP (Cps l) (Cps r) = eqP l r
  showP (Cps f) = "Cps (" ++ showP f ++ ")"
instance TestableProfunctor (Cps :: CAT (CPS (r :: Type))) where
  genProfunctorElt nm = do
    SomeP f <- genProfunctorElt @(->) nm
    pure (SomeP (Cps f))

instance Testable (CPS (r :: Type)) where
  type TestOb a = (Ob a, TestOb (UN C a))
  obFromTestOb r = r
  showOb @(C a) = "C " ++ showOb @_ @a
  genSome = genSomeDef @'[C Bool, C (), C (Maybe Bool)]
