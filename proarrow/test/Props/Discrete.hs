{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Discrete where

import Data.Type.Equality (type (:~:))
import Data.Type.Equality qualified as Eq
import Data.Type.Nat (SNat (..), snat)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Enriched.Thin
  ( DecidableProfunctor (..)
  , Decision (..)
  , Holds
  , Indexed (..)
  , KnownIndex
  , Objects
  , ThinProfunctor (..)
  )
import Proarrow.Category.Enriched.Thin.Composition (Closure)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Discrete (CODISCRETE (..), Codiscrete, DISCRETE (..), Discrete (..))
import Proarrow.Core (CAT, Profunctor (..), UN)

test :: TestTree
test =
  testGroup
    "Discrete"
    [ testProperty "reachability over a bare set finds the edge" $ withArr reachEdge (pure ())
    , testProperty "distinct points are decided apart" $ case decide @Discrete @(D FLS) @(D TRU) of
        No -> pure ()
    ]

-- | A point of the bare set @DISCRETE BOOL@ is recovered from its index alone.
pointOf :: forall (a :: DISCRETE BOOL). (KnownIndex a) => Booleans (UN D a) (UN D a)
pointOf = case snat @(Index a) of
  SZ -> Fls
  SS @i -> case snat @i of SZ -> Tru

-- | The graph with the single edge @FLS -> TRU@ on the bare two-point set: unlike over the walking
-- arrow, there is no base arrow to fall back on.
type Edge :: CAT (DISCRETE BOOL)
data Edge a b where
  FT :: Edge (D FLS) (D TRU)

instance Profunctor Edge where
  dimap Refl Refl e = e
  r \\ FT = r

type family EdgeHolds (a :: BOOL) (b :: BOOL) :: BOOL where
  EdgeHolds FLS TRU = TRU
  EdgeHolds a b = FLS

instance ThinProfunctor Edge

instance DecidableProfunctor Edge where
  type Holds Edge a b = EdgeHolds (UN D a) (UN D b)
  decide @a @b = case (pointOf @a, pointOf @b) of
    (Fls, Fls) -> No
    (Fls, Tru) -> Yes FT
    (Tru, Fls) -> No
    (Tru, Tru) -> No
  toHolds FT r = r

-- | The closure over the bare set: the edge is found, its reverse is not, and points reach themselves.
reachEdge :: Closure Edge (D FLS) (D TRU)
reachEdge = arr

noWayBack :: Holds (Closure Edge) (D TRU) (D FLS) :~: FLS
noWayBack = Eq.Refl

reachSelf :: Holds (Closure Edge) (D TRU) (D TRU) :~: TRU
reachSelf = Eq.Refl

-- | The discrete category itself is decided by comparing indices.
samePoint :: Holds (Discrete :: CAT (DISCRETE BOOL)) (D FLS) (D FLS) :~: TRU
samePoint = Eq.Refl

otherPoint :: Holds (Discrete :: CAT (DISCRETE BOOL)) (D FLS) (D TRU) :~: FLS
otherPoint = Eq.Refl

-- * The codiscrete category on the same points

-- | Its objects are the points of @k@, in the same order.
objectsCodiscrete :: Objects (CODISCRETE BOOL) :~: '[CD FLS, CD TRU]
objectsCodiscrete = Eq.Refl

-- | Every point reaches every other, and the closure computes that by searching the points -- which
-- only typechecks because the codiscrete category is enumerable.
codiscreteReaches :: Holds (Closure (Codiscrete :: CAT (CODISCRETE BOOL))) (CD TRU) (CD FLS) :~: TRU
codiscreteReaches = Eq.Refl
