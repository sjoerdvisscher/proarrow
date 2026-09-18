{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | (Co)equalizers, pullbacks and pushouts of finitary profunctors, on a small copresheaf over the
-- walking arrow: three rows at 'FLS', two at 'TRU', and 'F2T' carrying the first to the second.
-- The equalizer of the identity with the swap of two rows at 'FLS' is their fixed points, the
-- coequalizer identifies the swapped pair; the kernel pair of the merge of two rows at 'FLS' relates
-- exactly those two, its pushout along itself glues two copies of the rows at the merged ones, and its
-- image is the two rows it lands on. The exponentials and the subobject classifier are enumerated
-- too, which is what makes this an elementary topos.
module Props.Finitary (test) where

import Control.Monad (unless)
import Data.List (sort)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (Property, testFailed, testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (FIN, FINITARY, Finitary (..), elements, size)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), IsBool (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (Sub (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Topos (HasEpiMonoFactorization (..), isEq)
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Functor (Copresheaf)
import Proarrow.Limit.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks (..), kernelPair)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Exponential ((:~>:))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Testing (TestableType (..), TestingEqShow (..), optGen)
import Proarrow.Testing.Laws (propFinitary)
import Props.Bool ()

-- | The kind of finitary copresheaves on the walking arrow.
type Psh = FINITARY BOOL ()

type Rows :: Copresheaf BOOL
data Rows u b where
  R1, R2, R3 :: Rows '() FLS
  S1, S2 :: Rows '() TRU

deriving instance Eq (Rows u b)
deriving instance Ord (Rows u b)
deriving instance Show (Rows u b)

instance Profunctor Rows where
  dimap Unit Fls x = x
  dimap Unit Tru x = x
  dimap Unit F2T R1 = S1
  dimap Unit F2T R2 = S1
  dimap Unit F2T R3 = S2
  r \\ x = case x of
    R1 -> r
    R2 -> r
    R3 -> r
    S1 -> r
    S2 -> r

instance Finitary Rows where
  size @_ @b = case boolId @b of
    Fls -> 3
    Tru -> 2
  toIndex R1 = 0
  toIndex R2 = 1
  toIndex R3 = 2
  toIndex S1 = 0
  toIndex S2 = 1
  fromIndex @_ @b i = case boolId @b of
    Fls -> [R1, R2, R3] !! fromIntegral i
    Tru -> [S1, S2] !! fromIntegral i

instance (Ob u, Ob b) => TestingEqShow (Rows u b)

-- | Spelled out rather than taken from 'elements', so that 'propFinitary' checks the numbering
-- against something independent of it: a generator defined as @optGen elements@ can never produce a
-- row the instance has lost track of, which is exactly the mistake worth catching.
instance (Ob u, IsBool b) => TestableType (Rows u b) where
  gen = case boolId @b of
    Fls -> optGen [R1, R2, R3]
    Tru -> optGen [S1, S2]

-- | Swap the first two rows at 'FLS'. 'F2T' is onto, so naturality leaves no choice about the
-- component at 'TRU'; and the swap stays inside 'F2T'\'s fibres, so the component it forces is the
-- identity.
swapRows :: Prof Rows Rows
swapRows = Prof \case
  R1 -> R2
  R2 -> R1
  R3 -> R3
  S1 -> S1
  S2 -> S2

-- | Merge the first two rows at 'FLS'. As for 'swapRows', the component at 'TRU' is then forced to
-- be the identity -- not because every natural family is the identity there, but because this one is.
mergeRows :: Prof Rows Rows
mergeRows = Prof \case
  R2 -> R1
  x -> x

-- | Check a measured value against the expected one, showing what was found.
expect :: (Eq a, Show a) => String -> a -> a -> Property ()
expect what want got = unless (got == want) (testFailed (what ++ ", found " ++ show got))

-- | The sizes of @1 ~~> Rows@ and of @Rows@ at one object, which Yoneda says must agree.
yoneda :: forall (b :: BOOL). (IsBool b) => (Natural, Natural)
yoneda = (size @(TerminalProfunctor :~>: Rows) @'() @b, size @Rows @'() @b)

test :: TestTree
test =
  testGroup
    "Finitary"
    [ propFinitary @Rows "Rows"
    , testProperty "the equalizer of the identity and a swap is the fixed rows" $
        equalize @Psh @(FIN Rows) id (Sub swapRows) \(Sub (Prof @e incl)) -> do
          expect "both rows at TRU" 2 (size @e @'() @TRU)
          expect "the fixed row at FLS should be R3" [R3] (map incl (elements @e @'() @FLS))
    , testProperty "the kernel pair of a merge relates the merged rows" $
        kernelPair @Psh (Sub mergeRows) \l@(Sub (Prof @p p1)) r@(Sub (Prof p2)) -> do
          expect
            "the merged rows and the diagonal"
            [(R1, R1), (R1, R2), (R2, R1), (R2, R2), (R3, R3)]
            (sort [(p1 x, p2 x) | x <- elements @p @'() @FLS])
          expect "only the diagonal at TRU" [(S1, S1), (S2, S2)] [(p1 x, p2 x) | x <- elements @p @'() @TRU]
          -- The diagonal of 'Rows' is a cone over the kernel pair; factoring it through gives a section of
          -- either leg.
          case factorPullback @Psh l r id id of
            Sub (Prof diag) -> expect "the diagonal should factor through" [R1, R2, R3] (map (p1 . diag) (elements @Rows @'() @FLS))
    , testProperty "the coequalizer of the identity and a swap identifies the swapped rows" $
        coequalize @Psh @(FIN Rows) id (Sub swapRows) \(Sub (Prof @_ @c proj)) -> do
          expect "two classes at FLS" 2 (size @c @'() @FLS)
          expect "two classes at TRU" 2 (size @c @'() @TRU)
          expect "R1 and R2 identified, R3 apart" [0, 0, 1] (map (toIndex . proj) (elements @Rows @'() @FLS))
    , testProperty "the pushout of a merge along itself glues two copies at the merged rows" $
        pushout @Psh (Sub mergeRows) (Sub mergeRows) \l@(Sub (Prof @_ @p p1)) r@(Sub (Prof p2)) -> do
          expect "four classes at FLS" 4 (size @p @'() @FLS)
          expect "two classes at TRU" 2 (size @p @'() @TRU)
          -- The merged rows are glued, the two copies of R2 stay apart.
          expect
            "which rows the two copies share"
            [True, False, True]
            [toIndex (p1 x) == toIndex (p2 x) | x <- elements @Rows @'() @FLS]
          -- The merge itself, on both copies, is a cocone; factoring it gives a retraction of either leg.
          case factorPushout @Psh l r (Sub mergeRows) (Sub mergeRows) of
            Sub (Prof m) -> expect "the merge should factor through" [R1, R1, R3] (map (m . p1) (elements @Rows @'() @FLS))
    , testProperty "the image of a merge is the rows it lands on" $
        case factorize @Psh (Sub mergeRows) of
          Sub (Prof @_ @im epi) :.: Sub (Prof mono) -> do
            expect "two rows in the image at FLS" 2 (size @im @'() @FLS)
            expect "two rows in the image at TRU" 2 (size @im @'() @TRU)
            expect "mono after epi is the merge" [R1, R1, R3] (map (mono . epi) (elements @Rows @'() @FLS))
            expect "the epi part identifies R1 and R2" [0, 0, 1] (map (toIndex . epi) (elements @Rows @'() @FLS))
    , testProperty "the exponential by the terminal object is the profunctor itself" $ do
        -- Yoneda: @1 ~~> q@ is @Nat(y(a,b), q)@, which is @q@ at that point.
        expect "1 ~~> Rows should be Rows at FLS" (3, 3) (yoneda @FLS)
        expect "1 ~~> Rows should be Rows at TRU" (2, 2) (yoneda @TRU)
        expect "Rows ~~> 1 should be the terminal object" 1 (size @(Rows :~>: TerminalProfunctor) @'() @FLS)
    , testProperty "the exponential of the rows by themselves is enumerated" $ do
        -- Counted by hand: a natural family is a pair of maps commuting with 'F2T', so summing over
        -- the four possible components at TRU gives 4 + 8 + 1 + 2 at FLS; at TRU the map is free.
        expect
          "Rows ~~> Rows"
          (15, 4)
          (size @(Rows :~>: Rows) @'() @FLS, size @(Rows :~>: Rows) @'() @TRU)
        -- Every index round trips, so the enumeration is a bijection and every family it builds is
        -- natural: 'toIndex' rejects the families that are not.
        expect
          "the exponential's indices should round trip"
          [0 .. 14]
          (map (toIndex @(Rows :~>: Rows) @'() @FLS) (elements @(Rows :~>: Rows) @'() @FLS))
    , testProperty "the subobject classifier has the three truth values of the walking arrow" $
        expect "Omega" (3, 2) (size @Sieve @'() @FLS, size @Sieve @'() @TRU)
    , testProperty "equality of rows is classified, and R1 and R2 become equal later" $
        -- 'isEq' takes only the object: its kind argument is inferred.
        case isEq @(PR (FIN Rows)) of
          Prod (Sub (Prof eq)) -> do
            let at x y = case eq (x :*: y) of Sieve s -> (s id Fls, s id F2T)
            expect "a row is equal to itself everywhere" (True, True) (at R1 R1)
            -- The middle truth value: false now, true once the arrow has merged them.
            expect "R1 and R2 should become equal at TRU" (False, True) (at R1 R2)
            expect "R1 and R3 should stay apart" (False, False) (at R1 R3)
    ]
