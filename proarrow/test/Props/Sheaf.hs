{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Sheaves at two finite sites, chosen to differ in the two ways that matter.
--
-- 'ByArrow' covers 'TRU' by 'FLS' alone. A presheaf is a sheaf when restriction along the one
-- leg is a bijection, which 'Two' is; 'Proarrow.Category.Enriched.Finitary.Sheaf.isSheaf' agrees,
-- and separates the
-- representables -- the one at 'TRU' is a sheaf, the one at 'FLS' is not -- so this coverage is
-- /not/ subcanonical. That failure is the \"too few\" one: @'Yo' 'FLS'@ has one element at 'FLS'
-- and none at 'TRU', so the cover carries a matching family that nothing at 'TRU' restricts to.
--
-- 'Proarrow.Category.Sheaf.Canonical' covers the discrete two-point space by its singletons, and
-- the empty set by nothing at all. That empty cover is the interesting one: it forces a sheaf to
-- have exactly one section over the empty set, which is the only thing 'Const2' gets wrong -- and
-- it gets it wrong the other way round, the \"too many\" failure, having two sections over the
-- empty set where the empty cover admits exactly one matching family.
--
-- Unions of opens are colimits, so here every representable /presheaf/ is a sheaf and the coverage
-- /is/ subcanonical -- which two-sidedly it is not, since the empty cover wants one section over
-- the empty set at every object of @j@ and @'Yo' a ('OP' b)@ has none at an object @b@ misses.
--
-- Both topologies satisfy the Lawvere-Tierney laws, and at both the dense sieves are the covering
-- ones.
--
-- Note the @j@ arguments below. Sheaf theory is about presheaves, so the natural instantiation of
-- every law here is @j ~ ()@ -- and over the unit category the covariant action is trivial
-- (@'dimap' g h@ collapses to @'lmap' g@), which leaves half of a two-sided profunctor untested by
-- construction. That is not a hypothetical worry: the missing @'HasInitialObject'@ on
-- @'Proarrow.Category.Sheaf.Sheaf' 'Proarrow.Category.Sheaf.Sums'@ was exactly this kind of
-- covariant-side bug, and invisible at @j ~ ()@.
--
-- Only 'closure'\'s naturality and the two-sided 'isSheaf' verdicts are run at a non-trivial @j@,
-- though, because only they can see one. Both of the other laws are stated through
-- @'Proarrow.Category.Enriched.Finitary.Sheaf.isCovering'@, which is stable under @'rmap'@ whatever
-- the coverage, so at any @j@ they say exactly what they say at @()@.
module Props.Sheaf (test) where

import Data.Foldable (for_)
import Data.List (genericIndex, genericLength)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (Property, testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (Finitary (..), foreachOb, objIndex, sizes)
import Proarrow.Category.Enriched.Finitary.Sheaf (closure, isSheaf, lawvereTierney)
import Proarrow.Category.Enriched.Finitary.Topos (FIN, FINITARY)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), IsBool (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub)
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Sheaf (ByArrow, Canonical, Cover (..), Leg (..), Sheaf (..), Trivial, legArrow)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), lmap, obj, type (+->))
import Proarrow.Functor (Presheaf)
import Proarrow.Limit.BinaryProduct (PROD)
import Proarrow.Profunctor.Instance.Coproduct ((:+:))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Instance.Yoneda (Yo)
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genSomeDef
  , optGen
  , testEq
  )
import Proarrow.Testing.Laws
  ( propNaturalTransformation
  , testDenseIsCovering
  , testFinitary
  , testGeneratedSieveIsSieve
  , testGluesBack
  , testLawvereTierney_
  , testProfunctor
  , testSubobjectClassifier_
  )
import Props.Bool ()

type Two :: Presheaf BOOL
data Two b u where
  A, B :: Two TRU '()
  A', B' :: Two FLS '()

deriving instance Eq (Two b u)
deriving instance Show (Two b u)

instance Profunctor Two where
  dimap Tru Unit x = x
  dimap Fls Unit x = x
  dimap F2T Unit A = A'
  dimap F2T Unit B = B'
  r \\ x = case x of
    A -> r
    B -> r
    A' -> r
    B' -> r

instance Sheaf ByArrow Two where
  glue TruByFls m = case m ViaF2T of
    A' -> A
    B' -> B

-- | The elements at one object, in the order the numbering uses.
twos :: forall b. (IsBool b) => [Two b '()]
twos = case boolId @b of
  Fls -> [A', B']
  Tru -> [A, B]

instance Finitary Two where
  size @b @_ = genericLength (twos @b)
  toIndex A = 0
  toIndex B = 1
  toIndex A' = 0
  toIndex B' = 1
  fromIndex @b @_ i = twos @b `genericIndex` i
  elements @b @_ = twos @b

instance (Ob u, Ob b) => TestingEqShow (Two b u)

instance (Ob u, IsBool b) => TestableType (Two b u) where
  gen = case boolId @b of
    Fls -> optGen [A', B']
    Tru -> optGen [A, B]

instance TestableProfunctor Two

-- | Two elements at each object, but restriction collapses both of the ones at 'TRU' onto the same
-- element at 'FLS'. This is the case 'Proarrow.Category.Enriched.Finitary.Sheaf.isSheaf' exists to
-- catch and that no other fixture presents: the number of elements and the number of matching
-- families agree, so a verdict computed from the /counts/ would call it a sheaf, while restriction
-- is not injective and it is not one.
type Collapse :: Presheaf BOOL
data Collapse b u where
  C1, C2 :: Collapse TRU '()
  D1, D2 :: Collapse FLS '()

deriving instance Eq (Collapse b u)
deriving instance Show (Collapse b u)

instance Profunctor Collapse where
  dimap Tru Unit x = x
  dimap Fls Unit x = x
  dimap F2T Unit _ = D1
  r \\ x = case x of
    C1 -> r
    C2 -> r
    D1 -> r
    D2 -> r

collapses :: forall b. (IsBool b) => [Collapse b '()]
collapses = case boolId @b of
  Fls -> [D1, D2]
  Tru -> [C1, C2]

instance Finitary Collapse where
  size @b @_ = genericLength (collapses @b)
  toIndex C2 = 1
  toIndex D2 = 1
  toIndex _ = 0
  fromIndex @b @_ i = collapses @b `genericIndex` i
  elements @b @_ = collapses @b

instance (Ob u, Ob b) => TestingEqShow (Collapse b u)

instance (Ob u, IsBool b) => TestableType (Collapse b u) where
  gen = optGen (collapses @b)

instance TestableProfunctor Collapse

-- | The kind of finitary presheaves on the walking arrow, as a testable kind: objects from a palette,
-- shown by their tables of sizes, as "Props.Finitary" does for the copresheaves.
type Sh = FINITARY () BOOL

instance TestableProfunctor (Sub Prof :: CAT Sh)

instance Testable Sh where
  showOb @(SUB p) = show (sizes @p)
  genSome = genSomeDef @'[FIN Two, FIN (Yo TRU (OP '())), FIN (Yo FLS (OP '())), FIN (Sieve :: () +-> BOOL)]

-- * The two-point space

-- | A sheaf on the discrete two-point space: one section over the empty set, two over @{x}@, one
-- over @{y}@, and one per compatible pair over the whole space -- so two.
type Sections :: Presheaf (BOOL, BOOL)
data Sections u v where
  U0 :: Sections '(FLS, FLS) '()
  X1, X2 :: Sections '(TRU, FLS) '()
  Y1 :: Sections '(FLS, TRU) '()
  XY1, XY2 :: Sections '(TRU, TRU) '()

deriving instance Eq (Sections u v)
deriving instance Show (Sections u v)

instance Profunctor Sections where
  dimap (Fls :**: Fls) Unit s = s
  dimap (Tru :**: Fls) Unit s = s
  dimap (Fls :**: Tru) Unit s = s
  dimap (Tru :**: Tru) Unit s = s
  dimap (F2T :**: Fls) Unit _ = U0
  dimap (Fls :**: F2T) Unit _ = U0
  dimap (F2T :**: F2T) Unit _ = U0
  dimap (Tru :**: F2T) Unit XY1 = X1
  dimap (Tru :**: F2T) Unit XY2 = X2
  dimap (F2T :**: Tru) Unit _ = Y1
  r \\ s = case s of
    U0 -> r
    X1 -> r
    X2 -> r
    Y1 -> r
    XY1 -> r
    XY2 -> r

-- | Gluing over the two points pairs the sections; over the empty set there is nothing to glue and
-- one section to produce.
instance Sheaf Canonical Sections where
  glue ByPoints m = case (m AtX, m AtY) of
    (X1, Y1) -> XY1
    (X2, Y1) -> XY2
  glue ByNothing _ = U0

sections :: forall a. (Ob a) => [Sections a '()]
sections = case obj @a of
  Fls :**: Fls -> [U0]
  Tru :**: Fls -> [X1, X2]
  Fls :**: Tru -> [Y1]
  Tru :**: Tru -> [XY1, XY2]

instance Finitary Sections where
  size @a @_ = genericLength (sections @a)
  toIndex X2 = 1
  toIndex XY2 = 1
  toIndex _ = 0
  fromIndex @a @_ i = sections @a `genericIndex` i
  elements @a @_ = sections @a

instance (Ob u, Ob a) => TestingEqShow (Sections a u)
instance (Ob u, Ob a) => TestableType (Sections a u) where
  gen = optGen (sections @a)
instance TestableProfunctor Sections

-- | The constant presheaf with two sections everywhere, as the coproduct of two copies of the
-- one-section presheaf. It glues over the two points -- a matching pair is a diagonal one -- but it
-- has two sections over the empty set where a sheaf must have exactly one, so it is not a sheaf.
--
-- 'Two' is the same shape one site over: constant with two sections, and /is/ a sheaf for
-- 'ByArrow'. The difference is the empty cover, which 'ByArrow' does not have.
type Const2 :: Presheaf (BOOL, BOOL)
type Const2 = TerminalProfunctor :+: TerminalProfunctor

-- | The kind of finitary presheaves on the two-point space, as a testable kind.
type Sh2 = FINITARY () (BOOL, BOOL)

instance TestableProfunctor (Sub Prof :: CAT Sh2)

instance Testable Sh2 where
  showOb @(SUB p) = show (sizes @p)
  genSome = genSomeDef @'[FIN Sections, FIN Const2, FIN (Yo '(TRU, TRU) (OP '())), FIN (Sieve :: () +-> (BOOL, BOOL))]

test :: TestTree
test =
  testGroup
    "Sheaf"
    [ testProfunctor @Two
    , testProfunctor @Sections
    , testFinitary @Two "Two"
    , testFinitary @Sections "Sections"
    , -- the unique killer of a counts-only 'isSheaf', on a hand-written numbering
      testFinitary @Collapse "Collapse"
    , -- 'Sieve' is test infrastructure now: 'closure'\'s naturality quantifies over its 'elements'
      testFinitary @(Sieve :: BOOL +-> BOOL) "Sieve"
    , -- every 'Canonical' verdict runs through this numbering, and nothing was checking it
      testFinitary @(Booleans :**: Booleans) "BOOL x BOOL"
    , -- the only law suite that pins @'Omega' = 'Sieve'@ and @true = 'maximalSieve'@ as a
      -- classifier rather than by definition
      testSubobjectClassifier_ @(PROD Sh)
    , testSubobjectClassifier_ @(PROD Sh2)
    , testGroup
        "Trivial"
        [ -- With no covers, anything quantified over them asserts nothing while reporting successes,
          -- so @testGluesBack@, @isSheaf@ and @testGeneratedSieveIsSieve@ are all omitted here. What
          -- is left is a smoke test rather than a law suite: with no covers 'closure' is the
          -- identity on sieves, so the topology is the trivial one, and both of these hold of it by
          -- inspection. They still exercise the 'Omega' plumbing and the 'Sieve' equality the other
          -- two groups rely on.
          testLawvereTierney_ @(PROD Sh) (lawvereTierney @Trivial)
        , testDenseIsCovering @Trivial @() @BOOL
        ]
    , testGroup
        "ByArrow"
        [ testGluesBack @ByArrow @Two
        , testLawvereTierney_ @(PROD Sh) (lawvereTierney @ByArrow)
        , testProperty "restriction at TruByFls" $
            for_ ([A', B'] :: [Two FLS '()]) \m ->
              testEq
                "restriction"
                "lmap F2T (glue TruByFls (\\ViaF2T -> m))"
                (lmap (legArrow ViaF2T) (glue @ByArrow @Two TruByFls \ViaF2T -> m))
                "m"
                m
        , testProperty "isSheaf" $ do
            expect "Two is a sheaf" True (isSheaf @ByArrow @Two)
            expect "the representable at TRU is a sheaf" True (isSheaf @ByArrow @(Yo TRU (OP '())))
            expect "the representable at FLS is not: ByArrow is not subcanonical" False (isSheaf @ByArrow @(Yo FLS (OP '())))
            -- the counts agree here (2 elements, 2 matching families); only the tables differ
            expect "a collapsing restriction is not a sheaf" False (isSheaf @ByArrow @Collapse)
            -- the covariant side is a bystander: the same verdicts two-sidedly
            expect "Yo TRU (OP FLS) is a sheaf" True (isSheaf @ByArrow @(Yo TRU (OP FLS) :: BOOL +-> BOOL))
            expect "Yo FLS (OP TRU) is not" False (isSheaf @ByArrow @(Yo FLS (OP TRU) :: BOOL +-> BOOL))
        , testGluesBack @ByArrow @(Two :*: Two)
        , testProperty "closure under limits" $ do
            expect "a product of sheaves is a sheaf" True (isSheaf @ByArrow @(Two :*: Two))
            expect "the terminal profunctor is a sheaf" True (isSheaf @ByArrow @(TerminalProfunctor :: () +-> BOOL))
        , -- at @j = BOOL@, not @j = ()@: over the unit category @'dimap' g h@ collapses to
          -- @'lmap' g@, so a covariant slip in 'closure' would be invisible there
          testProperty "closure is natural" $
            propNaturalTransformation @(Sieve :: BOOL +-> BOOL) (closure @ByArrow)
        , testGeneratedSieveIsSieve @ByArrow @() @BOOL
        , testDenseIsCovering @ByArrow @() @BOOL
        ]
    , testGroup
        "Canonical"
        [ testGluesBack @Canonical @Sections
        , testLawvereTierney_ @(PROD Sh2) (lawvereTierney @Canonical)
        , testProperty "isSheaf" $ do
            expect "Sections is a sheaf" True (isSheaf @Canonical @Sections)
            expect "the constant presheaf is not: two sections over the empty set" False (isSheaf @Canonical @Const2)
            sequence_
              ( foreachOb @(BOOL, BOOL) @(Property ()) \ @a ->
                  [ expect
                      ("the representable at object " ++ show (objIndex @a) ++ " is a sheaf: Canonical is subcanonical")
                      True
                      (isSheaf @Canonical @(Yo a (OP '())))
                  ]
              )
            -- subcanonical is about the representable presheaves: two-sidedly the empty cover bites,
            -- since TRU has no arrow to FLS and so no section over the empty set there
            expect
              "the two-sided representable at '(TRU, FLS) over TRU is not a sheaf"
              False
              (isSheaf @Canonical @(Yo '(TRU, FLS) (OP TRU) :: BOOL +-> (BOOL, BOOL)))
        , testProperty "closure is natural" $
            propNaturalTransformation @(Sieve :: BOOL +-> (BOOL, BOOL)) (closure @Canonical)
        , testGeneratedSieveIsSieve @Canonical @() @(BOOL, BOOL)
        , testDenseIsCovering @Canonical @() @(BOOL, BOOL)
        ]
    ]
