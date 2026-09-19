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

import Data.List (genericIndex, genericLength, sort)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (Finitary (..), foreachOb)
import Proarrow.Category.Enriched.Finitary.Topos (FIN, FINITARY)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), IsBool (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Topos (HasEpiMonoFactorization (..), isEq)
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Functor (Copresheaf)
import Proarrow.Limit.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks (..), kernelPair)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Exponential ((:~>:))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genSomeDef
  , optGen
  )
import Proarrow.Testing.Laws
  ( propBinaryCoproducts_
  , propBinaryProducts_
  , propCategory
  , propClosed_
  , propCoequalizers_
  , propEqualizers_
  , propFinitary
  , propInitialObject
  , propPullbacks_
  , propPushouts_
  , propTerminalObject
  )
import Proarrow.Tools.DPO (Rule (..), dpoStep)
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

-- | The rows at one object, in the order the numbering below uses.
rows :: forall b. (IsBool b) => [Rows '() b]
rows = case boolId @b of
  Fls -> [R1, R2, R3]
  Tru -> [S1, S2]

instance Finitary Rows where
  size @_ @b = genericLength (rows @b)
  toIndex R1 = 0
  toIndex R2 = 1
  toIndex R3 = 2
  toIndex S1 = 0
  toIndex S2 = 1
  fromIndex @_ @b i = rows @b `genericIndex` i
  elements @_ @b = rows @b

instance (Ob u, Ob b) => TestingEqShow (Rows u b)

-- | Spelled out rather than taken from 'elements', so that 'propFinitary' checks the numbering
-- against something independent of it: a generator defined as @optGen elements@ can never produce a
-- row the instance has lost track of, which is exactly the mistake worth catching.
instance (Ob u, IsBool b) => TestableType (Rows u b) where
  gen = case boolId @b of
    Fls -> optGen [R1, R2, R3]
    Tru -> optGen [S1, S2]

-- | The copresheaf with one element at 'TRU' and none at 'FLS' -- a lone \"vertex\" for the
-- double-pushout tests. It is a subprofunctor of 'Rows' (nothing at 'FLS' can dangle off it).
type Point :: Copresheaf BOOL
data Point u b where
  Pt :: Point '() TRU

deriving instance Eq (Point u b)
deriving instance Show (Point u b)

instance Profunctor Point where
  dimap Unit Fls x = x
  dimap Unit Tru Pt = Pt
  dimap Unit F2T x = case x of {}
  r \\ Pt = r

instance Finitary Point where
  size @_ @b = genericLength (points @b)
  toIndex Pt = 0
  fromIndex @_ @b i = points @b `genericIndex` i
  elements @_ @b = points @b

points :: forall b. (IsBool b) => [Point '() b]
points = case boolId @b of
  Fls -> []
  Tru -> [Pt]

-- | One element at each object, the one at 'FLS' mapping to the one at 'TRU' -- the representable at
-- 'FLS', and the analogue of an edge together with its endpoint.
type Edge :: Copresheaf BOOL
data Edge u b where
  Src :: Edge '() FLS
  Tgt :: Edge '() TRU

deriving instance Eq (Edge u b)
deriving instance Show (Edge u b)

instance Profunctor Edge where
  dimap Unit Fls Src = Src
  dimap Unit Tru Tgt = Tgt
  dimap Unit F2T Src = Tgt
  r \\ x = case x of Src -> r; Tgt -> r

instance Finitary Edge where
  size = 1
  toIndex _ = 0
  fromIndex @_ @b i = case boolId @b of
    Fls -> [Src] !! fromIntegral i
    Tru -> [Tgt] !! fromIntegral i

-- | Two elements at 'FLS' sharing the one at 'TRU' -- two edges with a common endpoint.
type TwoEdges :: Copresheaf BOOL
data TwoEdges u b where
  A1, A2 :: TwoEdges '() FLS
  T :: TwoEdges '() TRU

deriving instance Eq (TwoEdges u b)
deriving instance Show (TwoEdges u b)

instance Profunctor TwoEdges where
  dimap Unit Fls x = x
  dimap Unit Tru x = x
  dimap Unit F2T A1 = T
  dimap Unit F2T A2 = T
  r \\ x = case x of A1 -> r; A2 -> r; T -> r

instance Finitary TwoEdges where
  size @_ @b = genericLength (twoEdges @b)
  toIndex A1 = 0
  toIndex A2 = 1
  toIndex T = 0
  fromIndex @_ @b i = twoEdges @b `genericIndex` i
  elements @_ @b = twoEdges @b

twoEdges :: forall b. (IsBool b) => [TwoEdges '() b]
twoEdges = case boolId @b of
  Fls -> [A1, A2]
  Tru -> [T]

-- | Both edges matched onto 'R3', which is an identification conflict: two elements the rule deletes
-- share an image, so no pushout complement exists.
bothOnR3 :: Prof TwoEdges Rows
bothOnR3 = Prof \case
  A1 -> R3
  A2 -> R3
  T -> S2

-- | The interface of 'Edge' that keeps only its endpoint.
tgtOnly :: Prof Point Edge
tgtOnly = Prof \Pt -> Tgt

-- | 'Edge' sitting on 'R3' and the 'S2' it maps to: deleting both leaves nothing dangling.
atR3 :: Prof Edge Rows
atR3 = Prof \case
  Src -> R3
  Tgt -> S2

-- | 'Point' sitting on the second element at 'TRU', which 'R3' maps onto.
atS2 :: Prof Point Rows
atS2 = Prof \Pt -> S2

-- * The category of finitary copresheaves, as a testable kind

instance TestableProfunctor (Sub Prof :: CAT Psh)

-- | Objects are picked from a list, exactly as 'Proarrow.Category.Instance.FinHask.FINHASK' does:
-- generating an arbitrary finitary profunctor would mean generating a type.
--
-- 'TestOb' is just 'Ob', with no 'Typeable': a profunctor is displayed by its table of sizes rather
-- than by a type name. That is what lets every property be used in its @prop..._@ form below: those
-- pass the constructions\' own object witnesses, which supply @Ob@ and nothing more, and @Ob@ is all
-- 'TestOb' asks for.
instance Testable Psh where
  showOb @(SUB p) = show (foreachOb @BOOL (\ @b -> [size @p @'() @b]))
  genSome = genSomeDef @'[FIN Rows, FIN Point, FIN Edge, FIN TwoEdges, FIN TerminalProfunctor]

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

-- | The sizes of @1 ~~> Rows@ and of @Rows@ at one object, which Yoneda says must agree.
yoneda :: forall (b :: BOOL). (IsBool b) => (Natural, Natural)
yoneda = (size @(TerminalProfunctor :~>: Rows) @'() @b, size @Rows @'() @b)

test :: TestTree
test =
  testGroup
    "Finitary"
    [ propCategory @Psh
    , propTerminalObject @Psh
    , propInitialObject @Psh
    , propBinaryProducts_ @Psh
    , propBinaryCoproducts_ @Psh
    , propClosed_ @(PROD Psh)
    , propEqualizers_ @Psh
    , propCoequalizers_ @Psh
    , propPullbacks_ @Psh
    , propPushouts_ @Psh
    , propFinitary @Rows "Rows"
    , -- The enumeration of natural transformations is itself a numbering, and obeys the same laws.
      -- Its generator draws from that same enumeration, so this checks the table round trip --
      -- tabulate a transformation built from a row and get the row back -- and not whether the
      -- enumeration is complete. The counts below are what check that.
      propFinitary @(Sub Prof :: CAT Psh) "Psh"
    , testProperty "the hom-sets have the sizes a hand count gives them" $ do
        -- 'F2T' is onto, so the component at TRU is forced; at FLS, R1 and R2 must land in a common
        -- fibre of it -- four ways inside {R1, R2}, or both on R3 -- and R3 is free: 5 * 3.
        expect "Rows -> Rows" 15 (size @(Sub Prof) @(FIN Rows) @(FIN Rows))
        -- 'Edge' is the representable at 'FLS', so Yoneda says this is the size of 'Rows' there.
        expect "Edge -> Rows" 3 (size @(Sub Prof) @(FIN Edge) @(FIN Rows))
        -- two edges share an endpoint, so their images share a fibre, as R1 and R2 did above
        expect "TwoEdges -> Rows" 5 (size @(Sub Prof) @(FIN TwoEdges) @(FIN Rows))
        -- 'Point' is empty at FLS, so only its one element at TRU has to go somewhere
        expect "Point -> Rows" 2 (size @(Sub Prof) @(FIN Point) @(FIN Rows))
        -- and nothing at FLS can receive the three rows
        expect "Rows -> Point" 0 (size @(Sub Prof) @(FIN Rows) @(FIN Point))
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
    , testProperty "deleting a row together with what it maps to has a pushout complement" $
        -- R3 and the S2 it maps to both go, so nothing is left dangling
        dpoStep
          (Rule (initiate @_ @(FIN Edge)) (initiate @_ @(FIN Edge)))
          (Sub atR3)
          ( \(Sub (Prof @d _)) _ _ -> do
              expect "R1 and R2 survive at FLS" 2 (size @d @'() @FLS)
              expect "only S1 survives at TRU" 1 (size @d @'() @TRU)
          )
          (testFailed "should have been glueable")
    , testProperty "a rule may delete a row and keep what it maps to" $
        -- the interface is the endpoint, so only R3 goes and both rows at TRU survive
        dpoStep
          (Rule (Sub tgtOnly) (id :: FIN Point ~> FIN Point))
          (Sub atR3)
          ( \(Sub (Prof @d _)) _ (Sub (Prof @_ @h _)) -> do
              expect "R1 and R2 survive at FLS" 2 (size @d @'() @FLS)
              expect "both rows survive at TRU" 2 (size @d @'() @TRU)
              -- gluing the kept endpoint back on is along an isomorphism, so the result matches
              expect "the result keeps two rows at FLS" 2 (size @h @'() @FLS)
              expect "the result keeps two rows at TRU" 2 (size @h @'() @TRU)
          )
          (testFailed "should have been glueable")
    , testProperty "an identification conflict between two deleted rows is refused" $
        -- both edges match onto R3, so the match identifies two elements the rule deletes
        dpoStep
          (Rule (initiate @_ @(FIN TwoEdges)) (initiate @_ @(FIN TwoEdges)))
          (Sub bothOnR3)
          (\_ _ _ -> testFailed "should not have been glueable")
          (pure ())
    , testProperty "the dangling condition fails when a surviving row points at a deleted one" $
        -- delete S2, which R3 maps onto: R3 would be left dangling
        dpoStep
          (Rule (initiate @_ @(FIN Point)) (initiate @_ @(FIN Point)))
          (Sub atS2)
          ( \_ _ _ ->
              testFailed "should not have been glueable"
          )
          (pure ())
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
