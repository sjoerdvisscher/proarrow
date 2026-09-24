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

import Data.List (genericIndex, genericLength)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, sizes)
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
import Proarrow.Category.Instance.Collage (COLLAGE (..), Collage (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Sheaf (ByElements, Cover (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), obj, (//), type (+->))
import Proarrow.Functor (Presheaf)
import Proarrow.Profunctor.Instance.Sieve (Sieve)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Instance.Yoneda (Yo)
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genElements
  , genSomeFinite
  , optGen
  )
import Proarrow.Testing.Laws (testCategory, testFinitary, testGluesBack, testSiteLaws)

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

-- | The coverage is 'ByElements', the generic one in "Proarrow.Category.Sheaf": the extra object
-- is covered by every arrow into it from the diamond. There are six legs (two out of each half and
-- two out of the intersection), and the last two factor through the first four, so the sieve is
-- the one four generating legs would give.
--
-- The two labelled alike agree on the intersection, so a matching family has equations to satisfy
-- along arrows a poset cannot tell apart, and it has them twice over.

-- | A profunctor on the collage, seen on the left layer only: the presheaf on the diamond that a
-- sheaf is determined by. Carries its objects, as 'Sieve' and 'Plus' do, so that @'Ob' a@ is
-- available directly. It cannot be recovered from @'Ob' ('L' a)@, which 'IsLR' takes as a premise
-- and does not give back.
type OnLeft :: forall {j} {k} {p :: k +-> j}. Presheaf (COLLAGE p) -> Presheaf j
data OnLeft s a d where
  OnLeft :: (Ob a, Ob d) => s (L a) d -> OnLeft s a d

instance (Profunctor s, CategoryOf j) => Profunctor (OnLeft (s :: Presheaf (COLLAGE (p :: k +-> j)))) where
  dimap f g (OnLeft x) = f // g // OnLeft (dimap (InL f) g x)
  r \\ OnLeft{} = r

instance (Finitary s, CategoryOf j) => Finitary (OnLeft (s :: Presheaf (COLLAGE (p :: k +-> j)))) where
  size @a @d = size @s @(L a) @d
  toIndex (OnLeft x) = toIndex x
  fromIndex @a @d i = OnLeft (fromIndex @s @(L a) @d i)
  elements @a @d = map OnLeft (elements @s @(L a) @d)

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

test :: TestTree
test =
  testGroup
    "Collage"
    [ testSiteLaws @ByElements @() @Patches
    , -- the first law test of the collage's own category structure, which this module is the
      -- first to make testable
      testCategory @Patches
    , testFinitary @(Collage :: CAT Patches) "Collage Pair"
    , testProperty "the shape of the site" $ do
        expect "two sections over each half, none over the top" [2, 2, 2, 0] (sizes @Pair)
        expect "the terminal presheaf is a sheaf" True (isSheaf @ByElements @(TerminalProfunctor :: Presheaf Patches))
        -- five objects, and a classifier far richer than any poset site here manages
        expect "sieves" [2, 3, 3, 6, 26] (sizes @(Sieve :: Presheaf Patches))
        expect "closed ones" [2, 3, 3, 6, 25] (sizes @(ClosedSieve ByElements :: Presheaf Patches))
    , -- What the site is for. Two sections of 'AtApex' at each of the six legs is 2^6 families;
      -- the overlaps cut them to the four that agree. On the poset sites an overlap gives one
      -- equation with no choice of arrow to satisfy it along, and on @ByEnds@ there is no overlap
      -- at all, so this is the first time the condition rules anything out.
      testProperty "matching is a real constraint" $ do
        expect
          "of which matching"
          (4 :: Natural)
          (withSieve (generatedSieve @ByElements @(R '()) @'() ByElements) \ @sub _ -> mapCount @sub @AtApex)
        -- and one section at the apex, so restriction is not the bijection a sheaf needs
        expect "the representable at the apex is no sheaf" False (isSheaf @ByElements @AtApex)
    , withTabulatedSheaf @ByElements @(Sheafify ByElements AtApex)
        ( \ @tab _ _ ->
            testGroup
              "its sheafification"
              [ testProperty "has one section at the apex per matching family" $
                  expect "sizes" [2, 2, 2, 0, 4] (sizes @tab)
              , -- The half of "a sheaf is its left layer" that the sheaf condition does not
                -- already give. isSheaf checks that a sheaf's value at the extra object is
                -- determined by its left part. This checks that restriction to the left layer
                -- loses no maps either (every presheaf map extends, and only one way), and nothing
                -- else here tests it. Together they say the sheaves on a ByElements site are the
                -- presheaves on its left layer, the right one carrying no information.
                testProperty "restriction to the left layer is fully faithful" $ do
                  expect
                    "the terminal sheaf to itself"
                    (mapCount @(TerminalProfunctor :: Presheaf Patches) @(TerminalProfunctor :: Presheaf Patches))
                    (mapCount @(OnLeft (TerminalProfunctor :: Presheaf Patches)) @(OnLeft (TerminalProfunctor :: Presheaf Patches)))
                  expect
                    "the terminal sheaf to the sheafification -- none, the top being empty"
                    (mapCount @(TerminalProfunctor :: Presheaf Patches) @tab)
                    (mapCount @(OnLeft (TerminalProfunctor :: Presheaf Patches)) @(OnLeft tab))
                  expect
                    "the sheafification to the terminal sheaf"
                    (mapCount @tab @(TerminalProfunctor :: Presheaf Patches))
                    (mapCount @(OnLeft tab) @(OnLeft (TerminalProfunctor :: Presheaf Patches)))
                  expect
                    "the sheafification to itself -- the four relabellings"
                    (mapCount @tab @tab)
                    (mapCount @(OnLeft tab) @(OnLeft tab))
                  -- and the control: on presheaves at large it is not full. 'AtApex' has one
                  -- section at the apex, so a self-map is pinned there, while its left part has
                  -- the same four relabellings as above, of which only one extends.
                  expect "the non-sheaf, on the collage" 1 (mapCount @AtApex @AtApex)
                  expect "the non-sheaf, on the left layer" 4 (mapCount @(OnLeft AtApex) @(OnLeft AtApex))
              , -- Gluing where matching rules families out: the search has four legs to satisfy
                -- and only a quarter of the families to choose from, a case no other test puts
                -- 'Proarrow.Category.Enriched.Finitary.Topos.glueBySearch'\'s uniqueness check and
                -- 'Proarrow.Category.Enriched.Finitary.Sheaf.gluePlus'\'s choice of factorisation
                -- to.
                testGluesBack @ByElements @tab
              ]
        )
        (error "the sheafification of the representable at the apex is not a sheaf")
    ]
