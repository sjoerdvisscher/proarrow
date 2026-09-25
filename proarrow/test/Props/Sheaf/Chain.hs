{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | __A site whose covers nest.__ In the other coverages here
-- @'Proarrow.Category.Sheaf.HasFiniteCovers'@'s Composition law (if @c@ covers @a@ and every leg of
-- @c@ is covered, the composites cover @a@) holds trivially. Either no leg of a cover is itself
-- covered (the two points of the discrete space, the bottom of the walking arrow), or every cover
-- of a leg contains its identity (the image of a functor). So the idempotence of 'closure' that
-- the law buys is never tested.
--
-- On the three-element chain @0 -> 1 -> 2@, 'Atomic' lets every arrow cover, so the law holds for
-- a reason: @1 '~>' 2@ covers @2@, its leg is covered by @0 '~>' 1@, and the composite @0 '~>' 2@
-- covers @2@ too. 'Pred' covers each object only by its immediate predecessor and breaks the law:
-- @0 '~>' 2@ is not a cover, so 'closure' is not idempotent, as the last test asserts. 'Pred'
-- still passes the three @testSiteLaws@ checks and the other two Lawvere-Tierney laws, so
-- idempotence is the only law separating the two coverages.
module Props.Sheaf.Chain (test) where

import Props.Bool ()
import Props.Ordinal ()
import Props.Sheaf ()

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (Finitary (..), sizes)
import Proarrow.Category.Enriched.Finitary.Sheaf (ClosedSieve, closure, isClosed, isSheaf, lawvereTierney)
import Proarrow.Category.Enriched.Finitary.Topos (FIN, FINITARY, glueBySearch)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Ordinal (LTE (..), ORDINAL (..), ORDINAL3)
import Proarrow.Category.Instance.Prof (Prof)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub)
import Proarrow.Category.Sheaf
  ( Atomic
  , Cover (..)
  , Coverage
  , Factors (..)
  , HasFiniteCovers (..)
  , Induced
  , Joins
  , Leg (..)
  , PulledBack (..)
  , Sheaf (..)
  , Site (..)
  , SomeCover (..)
  , SomeLeg (..)
  , StableSite (..)
  , glueExtension
  , pullbackAlongId
  )
import Proarrow.Core (CAT, Hom, Kind, Promonad (..), obj, type (+->))
import Proarrow.Functor (FunctorForRep (..), Presheaf)
import Proarrow.Limit.BinaryProduct (PROD)
import Proarrow.Profunctor.Corepresentable (Corep)
import Proarrow.Profunctor.Instance.Composition ((:.:))
import Proarrow.Profunctor.Instance.Coproduct ((:+:))
import Proarrow.Profunctor.Instance.Rift (Rift)
import Proarrow.Profunctor.Instance.Sieve (Sieve (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Instance.Yoneda (Yo)
import Proarrow.Testing (Testable (..), TestableProfunctor, expect, genSomeDef)
import Proarrow.Testing.Laws
  ( testAtomicIsDoubleNegation
  , testCoveredByImage
  , testGluesBack
  , testLawvereTierney_
  , testRanFullyFaithful
  , testRiftFullyFaithful
  , testSiteLaws
  )

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
type Pred :: Coverage
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

-- * The comparison lemma

-- | The chain's two ends, @0 '~>' 2@, as a functor from the walking arrow. Fully faithful, and
-- under 'Atomic' the middle is covered by @0 '~>' 1@, so the sheaves on the chain are the sheaves on
-- the walking arrow for the induced coverage. That coverage covers 'TRU' by @'FLS' '~>' 'TRU'@,
-- which is 'Atomic' again.
data family Ends :: BOOL +-> ORDINAL3

instance FunctorForRep Ends where
  type Ends @ FLS = O0
  type Ends @ TRU = O2
  fmap Fls = ZEQ
  fmap Tru = SLT (SLT ZEQ)
  fmap F2T = ZLT (ZLT ZEQ)

type EndsInc :: ORDINAL3 +-> BOOL
type EndsInc = Corep Ends

-- | The top two, @1 '~>' 2@. Dense in the categorical sense, since the bottom is the empty colimit,
-- but nothing from the image covers the bottom, and the lemma fails: the induced coverage gives
-- 'TRU' an empty cover, and its only sheaf is the terminal one.
data family Upper :: BOOL +-> ORDINAL3

instance FunctorForRep Upper where
  type Upper @ FLS = O1
  type Upper @ TRU = O2
  fmap Fls = SLT ZEQ
  fmap Tru = SLT (SLT ZEQ)
  fmap F2T = SLT (ZLT ZEQ)

type UpperInc :: ORDINAL3 +-> BOOL
type UpperInc = Corep Upper

-- | Two elements everywhere, on the walking arrow.
type Two :: Presheaf BOOL
type Two = TerminalProfunctor :+: TerminalProfunctor

-- | Two elements everywhere, on the chain.
type TwoC :: Presheaf ORDINAL3
type TwoC = TerminalProfunctor :+: TerminalProfunctor

instance Sheaf (Induced Atomic EndsInc) Two where
  glue = glueBySearch @(Induced Atomic EndsInc)

instance Sheaf Atomic (Rift (OP EndsInc) Two) where
  glue = glueExtension @Atomic

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
        , -- a chain has pullbacks, so here too the atomic topology is the double-negation one --
          -- on a site where, unlike the walking arrow, covers nest
          testAtomicIsDoubleNegation @ORDINAL3
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
        "restricted to its ends"
        [ testSiteLaws @(Induced Atomic EndsInc) @() @BOOL
        , testLawvereTierney_ @(PROD (FINITARY () BOOL)) (lawvereTierney @(Induced Atomic EndsInc))
        , testRanFullyFaithful @EndsInc
        , testCoveredByImage @Atomic @EndsInc
        , testGluesBack @Atomic @(Rift (OP EndsInc) Two)
        , testProperty "the comparison lemma" $ do
            expect
              "restriction keeps a sheaf"
              (True, True)
              (isSheaf @Atomic @TwoC, isSheaf @(Induced Atomic EndsInc) @(EndsInc :.: TwoC))
            expect
              "extension makes one"
              (True, True)
              (isSheaf @(Induced Atomic EndsInc) @Two, isSheaf @Atomic @(Rift (OP EndsInc) Two))
            expect "the extension" [2, 2, 2] (sizes @(Rift (OP EndsInc) Two))
            expect
              "the induced coverage has the sheaves of Atomic"
              (isSheaf @Atomic @Two, isSheaf @Atomic @(Yo FLS (OP '())), isSheaf @Atomic @(Yo TRU (OP '())))
              ( isSheaf @(Induced Atomic EndsInc) @Two
              , isSheaf @(Induced Atomic EndsInc) @(Yo FLS (OP '()))
              , isSheaf @(Induced Atomic EndsInc) @(Yo TRU (OP '()))
              )
        , testProperty "the ends are not dense" $
            expect
              "transformations 1 -> 0, arrows 1 -> 0"
              (1, 0)
              (size @(Rift (OP EndsInc) EndsInc) @O1 @O0, size @(Hom ORDINAL3) @O1 @O0)
        , testRiftFullyFaithful @UpperInc
        , testLawvereTierney_ @(PROD (FINITARY () BOOL)) (lawvereTierney @(Induced Atomic UpperInc))
        , testProperty "the top two are dense, but do not cover the bottom" $ do
            expect
              "restriction loses a sheaf"
              (True, False)
              (isSheaf @Atomic @TwoC, isSheaf @(Induced Atomic UpperInc) @(UpperInc :.: TwoC))
            expect "the induced coverage has no sheaf with two elements" False (isSheaf @(Induced Atomic UpperInc) @Two)
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
