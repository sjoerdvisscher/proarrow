{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The finite ordinals as an enumerable thin category: composing the order with itself is
-- transitivity, computed by searching the objects.
module Props.Ordinal where

import Data.Type.Equality ((:~:) (Refl))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Enriched.Thin (Holds, Objects, ThinProfunctor (..))
import Proarrow.Category.Enriched.Thin.Composition ()
import Proarrow.Category.Instance.Bool (BOOL (..))
import Proarrow.Category.Instance.Ordinal (LTE, ORDINAL (..), ORDINAL3)
import Proarrow.Core (CAT)
import Proarrow.Profunctor.Instance.Composition ((:.:))

test :: TestTree
test =
  testGroup
    "Ordinal"
    [ testProperty "composing the order searches the objects" $ withArr transitive (pure ())
    ]

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
