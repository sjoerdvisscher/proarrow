{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The finite ordinals as an enumerable thin category: composing the order with itself is
-- transitivity, computed by searching the objects.
module Props.Ordinal where

import Data.Type.Equality ((:~:) (Refl))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Enriched.Finitary (objIndex)
import Proarrow.Category.Enriched.Thin (Holds, Objects, ThinProfunctor (..))
import Proarrow.Category.Enriched.Thin.Composition ()
import Proarrow.Category.Instance.Bool (BOOL (..))
import Proarrow.Category.Instance.Ordinal (LTE, ORDINAL (..), ORDINAL3)
import Proarrow.Core (CAT, Ob)
import Proarrow.Profunctor.Instance.Composition ((:.:))
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genElements
  , genSomeFinite
  )
import Proarrow.Testing.Laws
  ( testBinaryCoproducts_
  , testBinaryProducts_
  , testCartesian_
  , testCategory
  , testCopyDiscard_
  , testDistributive_
  , testInitialObject
  , testMonoidal_
  , testSymMonoidal_
  , testTerminalObject
  )

test :: TestTree
test =
  testGroup
    "Ordinal"
    [ testProperty "composing the order searches the objects" $ withArr transitive (pure ())
    , -- the chain as a distributive lattice: meet the minimum and tensor, join the maximum
      testCategory @ORDINAL3
    , testTerminalObject @ORDINAL3
    , testInitialObject @ORDINAL3
    , testBinaryProducts_ @ORDINAL3
    , testBinaryCoproducts_ @ORDINAL3
    , testMonoidal_ @ORDINAL3
    , testSymMonoidal_ @ORDINAL3
    , testCopyDiscard_ @ORDINAL3
    , testCartesian_ @ORDINAL3
    , testDistributive_ @ORDINAL3
    ]

instance Testable ORDINAL3 where
  showOb @a = show (objIndex @a)
  genSome = genSomeFinite

instance (Ob a, Ob b) => TestableType (LTE (a :: ORDINAL3) b) where
  gen = genElements @LTE

-- | Thin, so parallel arrows are equal for free. Forcing is the one thing left to check.
instance (Ob a, Ob b) => TestingEqShow (LTE (a :: ORDINAL3) b) where
  eqP l r = l `seq` r `seq` pure True
  showP _ = show (objIndex @a) ++ "<=" ++ show (objIndex @b)

instance TestableProfunctor (LTE :: CAT ORDINAL3)

-- | The three ordinals, in order.
objectsOrdinal3 :: Objects ORDINAL3 :~: '[OZ, OS OZ, OS (OS OZ)]
objectsOrdinal3 = Refl

-- | Neither leg is representable, so the composite is decided by searching the middle ordinal:
-- @0 <= 2@ holds because it factors through @1@ (among others).
transitive :: ((LTE :.: LTE) :: CAT ORDINAL3) OZ (OS (OS OZ))
transitive = arr

-- | And there is no way back down.
notTransitive :: Holds ((LTE :.: LTE) :: CAT ORDINAL3) (OS (OS OZ)) OZ :~: FLS
notTransitive = Refl
