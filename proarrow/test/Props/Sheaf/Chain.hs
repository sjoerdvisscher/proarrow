{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | __A site whose covers nest.__ In every other coverage here the legs of a cover are objects
-- that nothing covers: the two points of the discrete space, the bottom of the walking arrow, the
-- left layer of a collage. So @'Proarrow.Category.Sheaf.HasFiniteCovers'@'s Composition law -- if
-- @c@ covers @a@ and every leg of @c@ is covered, the composites cover @a@ -- is satisfied there
-- with nothing to check, and the idempotence of 'closure' that it buys is never put to work.
--
-- A chain has nothing but nesting. Under the 'Atomic' coverage on the three-element chain every
-- arrow covers, so @1 '~>' 2@ covers @2@, its leg @1@ is covered by @0 '~>' 1@, and the composite
-- @0 '~>' 2@ has to cover @2@ as well -- which it does, being an arrow. That is the law holding for
-- a reason rather than for want of a witness.
--
-- 'Pred' below is the same chain covered only by immediate predecessors, and there the law has
-- something to say and says no: the composite @0 '~>' 2@ is not one of its covers, so 'closure' is
-- not idempotent -- the assertion this module ends with. Which is also what makes the 'Atomic'
-- group's Lawvere--Tierney laws worth running, because idempotence is the /only/ law here that
-- separates the two coverages. 'Pred' is stable, and it passes all three of the checks
-- @testSiteLaws@ makes and the other two Lawvere--Tierney laws.
module Props.Sheaf.Chain (test) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (sizes)
import Proarrow.Category.Enriched.Finitary.Sheaf (ClosedSieve, closure, isClosed, isSheaf, lawvereTierney)
import Proarrow.Category.Enriched.Finitary.Topos (FIN, FINITARY)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Ordinal (LTE (..), ORDINAL (..), ORDINAL3)
import Proarrow.Category.Instance.Prof (Prof)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub)
import Proarrow.Category.Sheaf
  ( Atomic
  , Cover (..)
  , Factors (..)
  , HasFiniteCovers (..)
  , Joins
  , Leg (..)
  , PulledBack (..)
  , Site (..)
  , SomeCover (..)
  , SomeLeg (..)
  , StableSite (..)
  , pullbackAlongId
  )
import Proarrow.Core (CAT, Kind, Promonad (..), obj)
import Proarrow.Functor (Presheaf)
import Proarrow.Limit.BinaryProduct (PROD)
import Proarrow.Profunctor.Instance.Sieve (Sieve (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Instance.Yoneda (Yo)
import Proarrow.Testing (Testable (..), TestableProfunctor, expect, genSomeDef)
import Proarrow.Testing.Laws (testLawvereTierney_, testSiteLaws)

-- | The bottom of the chain.
type O0 :: ORDINAL3
type O0 = OZ

-- | The middle.
type O1 :: ORDINAL3
type O1 = OS OZ

-- | The top.
type O2 :: ORDINAL3
type O2 = OS (OS OZ)

-- | The kind of finitary presheaves on the chain, as a testable kind: the Lawvere--Tierney laws
-- are stated on the presheaf classifier, so this is what carries them.
type PshChain :: Kind
type PshChain = FINITARY () ORDINAL3

instance TestableProfunctor (Sub Prof :: CAT PshChain)

instance Testable PshChain where
  showOb @(SUB p) = show (sizes @p)
  genSome =
    genSomeDef
      @'[ FIN TerminalProfunctor
        , FIN (Yo O2 (OP '()))
        , FIN (Yo O0 (OP '()))
        , FIN (Sieve :: Presheaf ORDINAL3)
        ]

-- * The chain covered by its immediate predecessors

-- | The coverage that covers each object by the one below it, and nothing else. Stable, and not
-- composing: see the module header.
type data Pred

-- | The name of both of 'Pred'\'s covers: @TwoByOne@ covers 'O2' by its one leg @FromOne@, and
-- @OneByZero@ covers 'O1' by @FromZero@.
type data ByPredecessor

instance Site Pred ORDINAL3 where
  data Cover Pred ORDINAL3 a c where
    TwoByOne :: Cover Pred ORDINAL3 O2 ByPredecessor
    OneByZero :: Cover Pred ORDINAL3 O1 ByPredecessor
  data Leg Pred ORDINAL3 a c x where
    FromOne :: Leg Pred ORDINAL3 O2 ByPredecessor O1
    FromZero :: Leg Pred ORDINAL3 O1 ByPredecessor O0
  legArrow FromOne = SLT (ZLT ZEQ)
  legArrow FromZero = ZLT ZEQ
  legs TwoByOne = [SomeLeg FromOne]
  legs OneByZero = [SomeLeg FromZero]

instance HasFiniteCovers Pred ORDINAL3 where
  covers @a = case obj @a of
    ZEQ -> []
    SLT ZEQ -> [SomeCover OneByZero]
    SLT (SLT ZEQ) -> [SomeCover TwoByOne]

-- | Stable: every arrow into 'O2' other than the identity already factors through @1 '~>' 2@,
-- because the chain is thin and @0 <= 1@.
instance StableSite Pred ORDINAL3 where
  pullbackCover TwoByOne (ZLT (ZLT ZEQ)) = AlreadyFactors (Factors FromOne (ZLT ZEQ))
  pullbackCover TwoByOne (SLT (ZLT ZEQ)) = AlreadyFactors (Factors FromOne id)
  pullbackCover TwoByOne (SLT (SLT ZEQ)) = pullbackAlongId TwoByOne
  pullbackCover OneByZero (ZLT ZEQ) = AlreadyFactors (Factors FromZero id)
  pullbackCover OneByZero (SLT ZEQ) = pullbackAlongId OneByZero

-- | The sieve at the top of the arrows out of the bottom: the one generated by @0 '~>' 2@, and the
-- witness that 'Pred' does not compose.
fromBottom :: Sieve (O2 :: ORDINAL3) '()
fromBottom = Sieve \g _ -> case g of
  ZLT _ -> True
  _ -> False

test :: TestTree
test =
  testGroup
    "Chain"
    [ testGroup
        "Atomic"
        [ testSiteLaws @Atomic @() @ORDINAL3
        , -- the payoff: idempotence and meet preservation on a site where composing covers
          -- actually produces a cover that was not one of the two being composed
          testLawvereTierney_ @(PROD PshChain) (lawvereTierney @Atomic)
        , testProperty "isSheaf" $ do
            expect
              "the terminal presheaf is a sheaf: every restriction of it is a bijection"
              True
              (isSheaf @Atomic @(TerminalProfunctor :: Presheaf ORDINAL3))
            expect
              "the representable at the top is a sheaf -- it is the terminal presheaf"
              True
              (isSheaf @Atomic @(Yo O2 (OP '())))
            expect
              "the representable at the bottom is not: nothing over 1, one thing over 0"
              False
              (isSheaf @Atomic @(Yo O0 (OP '())))
            expect
              "the sieves are not: four at the top, three at the middle"
              False
              (isSheaf @Atomic @(Sieve :: Presheaf ORDINAL3))
        , testProperty "the truth values" $ do
            expect
              "the sieves: two at the bottom, three at the middle, four at the top"
              [2, 3, 4]
              (sizes @(Sieve :: Presheaf ORDINAL3))
            expect
              "the closed ones: the empty sieve and the maximal one, at every object"
              [2, 2, 2]
              (sizes @(ClosedSieve Atomic :: Presheaf ORDINAL3))
            expect
              "so the truth values are constant, and a sheaf -- as the classifier of a topos of sheaves must be"
              True
              (isSheaf @Atomic @(ClosedSieve Atomic :: Presheaf ORDINAL3))
        ]
    , testGroup
        "Joins"
        [ -- on a chain no element but the bottom is the join of the ones below it, so the one
          -- cover is the bottom's empty one, and a sheaf is a presheaf with one element there
          testSiteLaws @Joins @() @ORDINAL3
        , testLawvereTierney_ @(PROD PshChain) (lawvereTierney @Joins)
        , testProperty "isSheaf" $ do
            expect "the terminal presheaf is a sheaf" True (isSheaf @Joins @(TerminalProfunctor :: Presheaf ORDINAL3))
            expect "the representable at the top is a sheaf" True (isSheaf @Joins @(Yo O2 (OP '())))
            expect "and so is the one at the bottom: subcanonical" True (isSheaf @Joins @(Yo O0 (OP '())))
            expect "the sieves are not: two at the bottom" False (isSheaf @Joins @(Sieve :: Presheaf ORDINAL3))
        ]
    , testGroup
        "Pred"
        [ -- stability, generated sieves, and dense = covering all hold; only composition fails,
          -- and none of the three sees it
          testSiteLaws @Pred @() @ORDINAL3
        , testProperty "the covers do not compose, so closure is not idempotent" $ do
            expect
              "{0 -> 2} is not closed: its closure adds 1 -> 2"
              False
              (isClosed @Pred fromBottom)
            expect
              "its closure adds 1 -> 2, whose own closure is maximal"
              False
              (isClosed @Pred (closure @Pred fromBottom))
        ]
    ]
