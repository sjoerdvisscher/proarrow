{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | __A site that is neither a poset nor overlap-free.__ The other coverages in @Props.Sheaf@ are
-- one or the other: @Overlapping@ has legs that meet, on a poset; @Examples.Graph@'s @ByEnds@ has
-- parallel legs that do not meet. Matching needs both: a family has to agree on the overlaps, and
-- which arrow it agrees along only matters when there is more than one.
--
-- The category is the collage of 'Pair': the diamond of opens on the left, one extra object on the
-- right, and the elements of 'Pair' (two out of each open) as the parallel cross-arrows. The
-- overlaps have to come from the diamond, since a collage's cross-arrows all go one way.
module Props.Sheaf.Collage (test) where

import Data.List (genericIndex, genericLength, sort)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, foreachOb, indices, sizes)
import Proarrow.Category.Enriched.Finitary.Sheaf
  ( ClosedSieve
  , Sheafify
  , generatedSieve
  , isSheaf
  , withSieve
  , withTabulatedSheaf
  )
import Proarrow.Category.Enriched.Finitary.Topos (natElements)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Collage (COLLAGE (..), Collage (..), InjL)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Sheaf (ByImage, Cover (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), obj, type (+->))
import Proarrow.Functor (Copresheaf, Presheaf)
import Proarrow.Profunctor.Corepresentable (Corep, Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:))
import Proarrow.Profunctor.Instance.Ran (Ran)
import Proarrow.Profunctor.Instance.Rift (Rift)
import Proarrow.Profunctor.Instance.Sieve (Sieve)
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Instance.Yoneda (Yo)
import Proarrow.Testing
  ( Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genElements
  , genSomeFinite
  , genSomeList
  , optGen
  )
import Proarrow.Testing.Laws
  ( testAdjunction
  , testCategory
  , testFinitary
  , testGluesBack
  , testRanFullyFaithful
  , testSiteLaws
  )

-- | Two sections over each half of the diamond and over their intersection, none over the whole.
-- Restriction to the intersection keeps the label, so the two @X@s agree there and so do the two
-- @Y@s. That agreement is the overlap the site is built for. There is nothing over the top, so the
-- top stays out of the coverage.
type Pair :: Presheaf (BOOL, BOOL)
data Pair u v where
  XW, YW :: Pair '(FLS, FLS) '()
  XU, YU :: Pair '(TRU, FLS) '()
  XV, YV :: Pair '(FLS, TRU) '()

instance Profunctor Pair where
  dimap (Fls :**: Fls) Unit x = x
  dimap (Tru :**: Fls) Unit x = x
  dimap (Fls :**: Tru) Unit x = x
  dimap (F2T :**: Fls) Unit XU = XW
  dimap (F2T :**: Fls) Unit YU = YW
  dimap (Fls :**: F2T) Unit XV = XW
  dimap (Fls :**: F2T) Unit YV = YW
  dimap (F2T :**: F2T) Unit x = case x of {}
  dimap (Tru :**: F2T) Unit x = case x of {}
  dimap (F2T :**: Tru) Unit x = case x of {}
  dimap (Tru :**: Tru) Unit x = x
  r \\ x = case x of XW -> r; YW -> r; XU -> r; YU -> r; XV -> r; YV -> r

-- | The elements over each object, in the order the numbering uses.
pairs :: forall u. (Ob u) => [Pair u '()]
pairs = case obj @u of
  Fls :**: Fls -> [XW, YW]
  Tru :**: Fls -> [XU, YU]
  Fls :**: Tru -> [XV, YV]
  Tru :**: Tru -> []

-- | Comparable and generable at its objects, as the generic 'Collage' instances in
-- "Proarrow.Testing" require of the profunctor a collage is built from.
deriving instance Eq (Pair u v)

deriving instance Show (Pair u v)

instance (Ob u, Ob v) => TestingEqShow (Pair u v)

instance (Ob u, Ob v) => TestableType (Pair u v) where
  gen = optGen (pairs @u)

instance Finitary Pair where
  size @u @_ = genericLength (pairs @u)
  toIndex x = case x of XW -> 0; YW -> 1; XU -> 0; YU -> 1; XV -> 0; YV -> 1
  fromIndex @u @_ i = pairs @u `genericIndex` i
  elements @u @_ = pairs @u

-- | The collage: the diamond, one further object, and 'Pair' as the arrows into it.
type Patches = COLLAGE Pair

-- | The inclusion of the diamond as the left layer of the collage, as a corepresentable.
type Inc :: Patches +-> (BOOL, BOOL)
type Inc = Corep (InjL Pair)

-- | The coverage: every object is covered by the arrows into it from the diamond. At the extra
-- object that is six legs (two out of each half and two out of the intersection), and the last two
-- factor through the first four. The two labelled alike agree on the intersection, so a matching
-- family has equations to satisfy along arrows a poset cannot tell apart, and it has them twice
-- over.
type Cov = ByImage Inc

-- | Whether the adjunction's unit is a bijection at each object: its images, as indices, are all of them.
unitIsBijective :: forall (s :: Presheaf Patches). (Finitary s) => [Bool]
unitIsBijective = case corepUniv @(Star ExtendF) @s of
  Star (Prof unit) -> foreachOb @Patches \ @x -> foreachOb @() \ @c ->
    let ix = toIndex @(Rift (OP Inc) (Inc :.: s)) @x @c
    in [sort [ix (unit y) | y <- elements @s @x @c] == indices (size @(Rift (OP Inc) (Inc :.: s)) @x @c)]

-- | Extension along 'Inc', as a functor between the two categories of presheaves.
type ExtendF :: Presheaf (BOOL, BOOL) -> Presheaf Patches
type ExtendF = Rift (OP Inc)

-- | The finitary presheaves on the diamond and on the collage, as testable kinds, so that
-- @'Star' 'ExtendF'@ can be law-checked as an 'Proarrow.Adjunction.Adjunction'.
instance TestableProfunctor (Prof :: CAT (Presheaf (BOOL, BOOL)))

instance Testable (Presheaf (BOOL, BOOL)) where
  type TestOb p = Finitary p
  showOb @p = show (sizes @p)
  genSome = genSomeList "Presheaf (BOOL, BOOL)" [Some @Pair, Some @(TerminalProfunctor :: Presheaf (BOOL, BOOL))]

instance TestableProfunctor (Prof :: CAT (Presheaf Patches))

instance Testable (Presheaf Patches) where
  type TestOb p = Finitary p
  showOb @p = show (sizes @p)
  genSome =
    genSomeList "Presheaf Patches" [Some @AtApex, Some @(TerminalProfunctor :: Presheaf Patches)]

instance TestableProfunctor (Star ExtendF)

-- | The finitary copresheaves on the diamond and on the collage, as testable kinds, so that
-- @'Star' ('Ran' ('OP' 'Inc'))@ can be law-checked as an 'Proarrow.Adjunction.Adjunction'. By
-- Yoneda @'Ran' ('OP' 'Inc') p@ at @b@ is @p@ at @'L' b@, so on copresheaves it is restriction,
-- and its left adjoint @- ':.:' 'Inc'@ is the left Kan extension.
instance TestableProfunctor (Prof :: CAT (Copresheaf (BOOL, BOOL)))

instance Testable (Copresheaf (BOOL, BOOL)) where
  type TestOb p = Finitary p
  showOb @p = show (sizes @p)
  genSome =
    genSomeList
      "Copresheaf (BOOL, BOOL)"
      [ Some @(Yo '() (OP '(FLS, FLS)))
      , Some @(Yo '() (OP '(TRU, FLS)))
      , Some @(TerminalProfunctor :: Copresheaf (BOOL, BOOL))
      ]

instance TestableProfunctor (Prof :: CAT (Copresheaf Patches))

instance Testable (Copresheaf Patches) where
  type TestOb p = Finitary p
  showOb @p = show (sizes @p)
  genSome =
    genSomeList
      "Copresheaf Patches"
      [Some @(Yo '() (OP (L '(FLS, FLS)))), Some @(Yo '() (OP (R '()))), Some @(TerminalProfunctor :: Copresheaf Patches)]

-- | Restriction of copresheaves along 'Inc', written as a right Kan extension.
type RanInc :: Copresheaf Patches -> Copresheaf (BOOL, BOOL)
type RanInc = Ran (OP Inc)

instance TestableProfunctor (Star RanInc)

-- | How many natural transformations there are from one finitary profunctor to another.
mapCount :: forall {j} {k} (x :: j +-> k) (y :: j +-> k). (Finitary x, Finitary y, FiniteCat j, FiniteCat k) => Natural
mapCount = genericLength (natElements @x @y)

-- | Compared and shown by its index. Within one hom-set the objects determine the constructor, so
-- the index is faithful, as for 'Proarrow.Category.Enriched.Finitary.Topos.Tabulated'.
--
-- Pinned to this collage: 'TestableProfunctor'\'s quantified superclass needs the instance at
-- /abstract/ objects, and a shape-agnostic instance would need nested quantified constraints,
-- which GHC will not discharge through the product kind's object decomposition.
instance (Ob a, Ob b) => TestingEqShow (Collage (a :: Patches) b) where
  eqP f g = pure (toIndex @(Collage :: CAT Patches) f == toIndex g)
  showP f = show (toIndex @(Collage :: CAT Patches) f)

instance (Ob a, Ob b) => TestableType (Collage (a :: Patches) b) where
  gen = genElements @(Collage :: CAT Patches)

instance TestableProfunctor (Collage :: CAT Patches)

instance Testable Patches where
  showOb @a = case obj @a of
    InL (Fls :**: Fls) -> "W"
    InL (Tru :**: Fls) -> "U"
    InL (Fls :**: Tru) -> "V"
    InL (Tru :**: Tru) -> "top"
    InR Unit -> "R"
  genSome = genSomeFinite

-- | The representable at the extra object: two arrows into it out of each half, and one out of
-- the object itself. It witnesses that matching has content here (see the test below).
type AtApex :: Presheaf Patches
type AtApex = Yo (R '()) (OP '())

-- | 'Pair' extended to the whole collage: 'Pair' on the left layer, and at the apex the right Kan
-- lift of 'Pair' along itself, its four relabellings.
type Extended :: Presheaf Patches
type Extended = ExtendF Pair

test :: TestTree
test =
  testGroup
    "Collage"
    [ testSiteLaws @Cov @() @Patches
    , -- the first law test of the collage's own category structure, which this module is the
      -- first to make testable
      testCategory @Patches
    , testRanFullyFaithful @Inc
    , -- not dense: at the apex there are four transformations (the relabellings of Pair) and one
      -- arrow, which is why the representable at the apex is no sheaf
      testProperty "the diamond is not dense in the collage" $
        expect
          "transformations and arrows at the apex"
          (4, 1)
          (size @(Rift (OP Inc) Inc) @(R '()) @(R '()), size @(Collage :: CAT Patches) @(R '()) @(R '()))
    , testFinitary @(Collage :: CAT Patches) "Collage Pair"
    , testProperty "the shape of the site" $ do
        expect "two sections over each half, none over the top" [2, 2, 2, 0] (sizes @Pair)
        expect "the terminal presheaf is a sheaf" True (isSheaf @Cov @(TerminalProfunctor :: Presheaf Patches))
        -- five objects, and a classifier far richer than any poset site here manages
        expect "sieves" [2, 3, 3, 6, 26] (sizes @(Sieve :: Presheaf Patches))
        expect "closed ones" [2, 3, 3, 6, 25] (sizes @(ClosedSieve Cov :: Presheaf Patches))
    , -- What the site is for. Two sections of 'AtApex' at each of the six legs is 2^6 families;
      -- the overlaps cut them to the four that agree. On the poset sites an overlap gives one
      -- equation with no choice of arrow to satisfy it along, and on @ByEnds@ there is no overlap
      -- at all, so this is the first time the condition rules anything out.
      testProperty "matching is a real constraint" $ do
        expect
          "of which matching"
          (4 :: Natural)
          (withSieve (generatedSieve @Cov @(R '()) @'() Images) \ @sub _ -> mapCount @sub @AtApex)
        -- and one section at the apex, so restriction is not the bijection a sheaf needs
        expect "the representable at the apex is no sheaf" False (isSheaf @Cov @AtApex)
    , testGroup
        "extending a presheaf on the left layer"
        [ testProperty "gives a sheaf with the presheaf on the left" $ do
            expect "Pair on the left, the four relabellings at the apex" [2, 2, 2, 0, 4] (sizes @Extended)
            expect "a sheaf" True (isSheaf @Cov @Extended)
            expect "restricted to the left layer it is Pair again" (sizes @Pair) (sizes @(Inc :.: Extended))
            -- the coend Inc :.: s is computed generically; by coYoneda it is s at the left layer
            expect "the restriction of the apex's representable is Pair" (sizes @Pair) (sizes @(Inc :.: AtApex))
            -- the unit s -> Rift (OP Inc) (Inc :.: s) is an iso exactly on the sheaves
            expect "the unit is a bijection on it" True (and (unitIsBijective @Extended))
            expect "but not on the representable at the apex, which is no sheaf" False (and (unitIsBijective @AtApex))
        , -- Extension is right adjoint to restriction: a map into the extension is a map into Pair
          -- from the left layer. This is the universal property of the right Kan lift.
          testProperty "is right adjoint to restriction" $ do
            expect "from the apex's representable" (mapCount @(Inc :.: AtApex) @Pair) (mapCount @AtApex @Extended)
            expect
              "from the terminal presheaf"
              (mapCount @(Inc :.: (TerminalProfunctor :: Presheaf Patches)) @Pair)
              (mapCount @(TerminalProfunctor :: Presheaf Patches) @Extended)
            expect "from itself" (mapCount @(Inc :.: Extended) @Pair) (mapCount @Extended @Extended)
        , testAdjunction @(Star ExtendF) (\r -> r) (\r -> r)
        , -- and on copresheaves, restriction with the left Kan extension as its left adjoint
          testAdjunction @(Star RanInc) (\r -> r) (\r -> r)
        , testFinitary @Extended "the extension of Pair"
        , testGluesBack @Cov @Extended
        ]
    , withTabulatedSheaf @Cov @(Sheafify Cov AtApex)
        ( \ @tab _ _ ->
            testGroup
              "its sheafification"
              [ testProperty "has one section at the apex per matching family" $ do
                  expect "sizes" [2, 2, 2, 0, 4] (sizes @tab)
                  -- the same sheaf, built by the plus construction twice instead of by the Kan lift
                  expect "and the unit into that extension is a bijection" True (and (unitIsBijective @tab))
              , -- The half of "a sheaf is its left layer" that the sheaf condition does not
                -- already give. isSheaf checks that a sheaf's value at the extra object is
                -- determined by its left part. This checks that restriction to the left layer
                -- loses no maps either (every presheaf map extends, and only one way). Together they say the sheaves on this site are the
                -- presheaves on its left layer, the right one carrying no information.
                testProperty "restriction to the left layer is fully faithful" $ do
                  expect
                    "the terminal sheaf to itself"
                    (mapCount @(TerminalProfunctor :: Presheaf Patches) @(TerminalProfunctor :: Presheaf Patches))
                    (mapCount @(Inc :.: (TerminalProfunctor :: Presheaf Patches)) @(Inc :.: (TerminalProfunctor :: Presheaf Patches)))
                  expect
                    "the terminal sheaf to the sheafification -- none, the top being empty"
                    (mapCount @(TerminalProfunctor :: Presheaf Patches) @tab)
                    (mapCount @(Inc :.: (TerminalProfunctor :: Presheaf Patches)) @(Inc :.: tab))
                  expect
                    "the sheafification to the terminal sheaf"
                    (mapCount @tab @(TerminalProfunctor :: Presheaf Patches))
                    (mapCount @(Inc :.: tab) @(Inc :.: (TerminalProfunctor :: Presheaf Patches)))
                  expect
                    "the sheafification to itself -- the four relabellings"
                    (mapCount @tab @tab)
                    (mapCount @(Inc :.: tab) @(Inc :.: tab))
                  -- and the control: on presheaves at large it is not full. 'AtApex' has one
                  -- section at the apex, so a self-map is pinned there, while its left part has
                  -- the same four relabellings as above, of which only one extends.
                  expect "the non-sheaf, on the collage" 1 (mapCount @AtApex @AtApex)
                  expect "the non-sheaf, on the left layer" 4 (mapCount @(Inc :.: AtApex) @(Inc :.: AtApex))
              , -- Gluing where matching rules families out: the search has four legs to satisfy
                -- and only a quarter of the families to choose from, a case no other test puts
                -- 'Proarrow.Category.Enriched.Finitary.Topos.glueBySearch'\'s uniqueness check and
                -- 'Proarrow.Category.Enriched.Finitary.Sheaf.gluePlus'\'s choice of factorisation
                -- to.
                testGluesBack @Cov @tab
              ]
        )
        (error "the sheafification of the representable at the apex is not a sheaf")
    ]
