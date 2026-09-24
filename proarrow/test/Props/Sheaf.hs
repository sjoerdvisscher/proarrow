{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Sheaves for the library's generic coverages at two small categories, and for one coverage of
-- this module's own.
--
-- 'Atomic' on the walking arrow covers 'TRU' by 'FLS' -- and every object by its identity, which
-- decides nothing. A presheaf is a sheaf when restriction along 'F2T' is a bijection, which 'Two'
-- is; 'Proarrow.Category.Enriched.Finitary.Sheaf.isSheaf' agrees, and separates the
-- representables -- the one at 'TRU' is a sheaf, the one at 'FLS' is not -- so this coverage is
-- /not/ subcanonical. That failure is the \"too few\" one: @'Yo' 'FLS'@ has one element at 'FLS'
-- and none at 'TRU', so the cover carries a matching family that nothing at 'TRU' restricts to.
--
-- 'Joins' on @(BOOL, BOOL)@, the opens of the discrete two-point space, covers the whole space by
-- its singletons, and the empty set by nothing at all. That empty cover is the interesting one: it
-- forces a sheaf to have exactly one section over the empty set, which is the only thing 'Const2'
-- gets wrong -- and it gets it wrong the other way round, the \"too many\" failure, having two
-- sections over the empty set where the empty cover admits exactly one matching family.
--
-- Unions of opens are colimits, so here every representable /presheaf/ is a sheaf and the coverage
-- /is/ subcanonical -- which two-sidedly it is not, since the empty cover wants one section over
-- the empty set at every object of @j@ and @'Yo' a ('OP' b)@ has none at an object @b@ misses.
--
-- 'Overlapping', written by hand below, is the same four opens read so that the two halves
-- overlap: 'Joins' without the empty family. No generic coverage gives it, and it is here because
-- it is the one poset site whose gluing is an equalizer rather than a product.
--
-- All three topologies satisfy the Lawvere-Tierney laws, and at all three the dense sieves are the
-- covering ones.
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

import Examples.Graph (ByEnds, GRAPH (..))
import Proarrow.Category.Enriched.Finitary (Finitary (..), foreachOb, objIndex, sizes)
import Proarrow.Category.Enriched.Finitary.Sheaf
  ( ClosedSieve
  , Plus
  , SHEAVES
  , SHF
  , Sheafify
  , closure
  , isSheaf
  , lawvereTierney
  , withTabulatedSheaf
  )
import Proarrow.Category.Enriched.Finitary.Topos (FIN, FINITARY)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), IsBool (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub)
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Sheaf
  ( Atomic
  , Cover (..)
  , Factors (..)
  , HasFiniteCovers (..)
  , Joins
  , Leg (..)
  , PulledBack (..)
  , Sheaf (..)
  , Site (..)
  , SomeCover (..)
  , SomeLeg (..)
  , StableSite (..)
  , Trivial
  , factorThroughCover
  , pullbackAlongId
  )
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), lmap, obj, type (+->))
import Proarrow.Functor (Presheaf)
import Proarrow.Limit.BinaryProduct (PROD)
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Exponential ((:~>:))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo)
import Proarrow.Testing
  ( Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genSomeDef
  , genSomeList
  , optGen
  , testEq
  )
import Proarrow.Testing.Laws
  ( propNaturalTransformation
  , testBinaryCoproducts_
  , testBinaryProducts_
  , testCategory
  , testClosed_
  , testCoequalizers_
  , testDenseIsCovering
  , testEpiMonoFactorization_
  , testEqualizersAreSheaves
  , testEqualizers_
  , testFinitary
  , testGluesBack
  , testInitialObject
  , testLawvereTierney_
  , testPlusFixes
  , testProfunctor
  , testPullbacks_
  , testPushouts_
  , testSheafification
  , testSiteLaws
  , testSubobjectClassifier_
  , testTerminalObject
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

-- | Every arrow covers, so there are three covers: the two identities, glued by taking the one
-- leg's element, and 'F2T', glued by undoing the restriction.
instance Sheaf Atomic Two where
  glue (Solely f) m = case f of
    Fls -> m (Only Fls)
    Tru -> m (Only Tru)
    F2T -> case m (Only F2T) of
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
  genSome = genSomeDef @'[FIN Two, FIN (Yo TRU (OP '())), FIN (Yo FLS (OP '())), FIN (Sieve :: Presheaf BOOL)]

-- | The category of sheaves for 'Atomic', as a testable kind. Its objects need a 'Sheaf' /instance/,
-- not just a true 'isSheaf', which 'withTabulatedSheaf' supplies for anything that is one -- and
-- decides the condition on the way, so the failure branches below are where this palette asserts
-- that its members are sheaves at all. The representable at 'TRU' has no instance of its own and
-- enters tabulated, and so does the sheafification, whose own 'toIndex' re-runs the plus
-- construction (a minute at 'ShC' untabulated).
-- No product in the palette: the pullback laws would form pullbacks of products of products
-- (@'Two' ':*:' 'Two'@ here took the group from under 4s to 11s).
type ShB = SHEAVES Atomic () BOOL

instance TestableProfunctor (Sub Prof :: CAT ShB)

instance Testable ShB where
  showOb @(SUB p) = show (sizes @p)
  genSome =
    withTabulatedSheaf @Atomic @(Sheafify Atomic Collapse)
      ( \ @sheafified _ _ ->
          withTabulatedSheaf @Atomic @(Yo TRU (OP '()))
            ( \ @yoTru _ _ ->
                genSomeList
                  "ShB"
                  [ Some @(SHF Atomic Two)
                  , Some @(SHF Atomic TerminalProfunctor)
                  , Some @(SHF Atomic sheafified)
                  , Some @(SHF Atomic yoTru)
                  ]
            )
            (error "ShB: the representable at TRU is not a sheaf")
      )
      (error "ShB: the sheafification of Collapse is not a sheaf")

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

-- | A section over an open is its sections at the points. A point is join-prime -- it lies below
-- a join only by lying below one of the joined -- so every cover of an open has a leg over each
-- of its points, and @at@ reads the family there. Only @{x}@ has two sections, so it is the only
-- point that has to be read; over the empty set there is nothing to glue and one section to
-- produce.
instance Sheaf Joins Sections where
  glue @a c m = case obj @a of
    Fls :**: Fls -> U0
    Tru :**: Fls -> at (Tru :**: Fls)
    Fls :**: Tru -> Y1
    Tru :**: Tru -> case at (Tru :**: F2T) of
      X1 -> XY1
      X2 -> XY2
    where
      at :: forall x. x ~> a -> Sections x '()
      at h = case factorThroughCover c h of
        Just (Factors l u) -> lmap u (m l)
        Nothing -> error "Sections: no leg over the point, so the family is not over a cover"

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
-- 'Atomic'. The difference is the empty cover, which 'Atomic' does not have.
type Const2 :: Presheaf (BOOL, BOOL)
type Const2 = TerminalProfunctor :+: TerminalProfunctor

-- * The two-point space with overlapping halves

-- | The same four opens as 'Joins' at @(BOOL, BOOL)@, read as a space whose two halves /overlap/: @'(TRU, TRU)@
-- is covered by @'(TRU, FLS)@ and @'(FLS, TRU)@ as before, but @'(FLS, FLS)@ is now their
-- intersection rather than the empty set, and gets no cover of its own. Several coverages on one
-- category is what the @t@ parameter is for, and this is the pair that shows why it earns its
-- keep: same category, same cover, different sheaves.
--
-- The difference is the whole of what an overlap does. Under 'Joins' the two legs meet only at
-- the empty set, so a matching family is /any/ pair of sections and gluing is a product; here they
-- meet at a section of @p '(FLS, FLS)@, so a matching family is a pair that /agrees/ there and
-- gluing is an equalizer. The constant presheaf with two values is the shortest witness: it is no
-- sheaf for 'Joins' -- the empty cover wants one section over the empty set and it has two --
-- and it is one here, its four pairs of local sections cut down to the two that agree.
--
-- Stable and composing, so this is a Grothendieck topology: a cover pulls back along any arrow
-- into @'(TRU, TRU)@ to the target's identity cover, which factors through whichever leg the
-- arrow already factors through.
type data Overlapping

-- | The name of 'Overlapping'\'s one cover, whose 'Cover' constructor is @ByHalves@ and whose
-- 'Leg' constructors are @AtFst@ and @AtSnd@.
type data Halves

instance Site Overlapping (BOOL, BOOL) where
  data Cover Overlapping (BOOL, BOOL) a c where
    ByHalves :: Cover Overlapping (BOOL, BOOL) '(TRU, TRU) Halves
  data Leg Overlapping (BOOL, BOOL) a c x where
    AtFst :: Leg Overlapping (BOOL, BOOL) '(TRU, TRU) Halves '(TRU, FLS)
    AtSnd :: Leg Overlapping (BOOL, BOOL) '(TRU, TRU) Halves '(FLS, TRU)
  legArrow AtFst = Tru :**: F2T
  legArrow AtSnd = F2T :**: Tru
  legs ByHalves = [SomeLeg AtFst, SomeLeg AtSnd]

-- | As 'Joins', minus the empty cover: the intersection factors through either half, and
-- through the first by choice.
instance StableSite Overlapping (BOOL, BOOL) where
  pullbackCover ByHalves (Tru :**: Tru) = pullbackAlongId ByHalves
  pullbackCover ByHalves (Tru :**: F2T) = AlreadyFactors (Factors AtFst id)
  pullbackCover ByHalves (F2T :**: Tru) = AlreadyFactors (Factors AtSnd id)
  pullbackCover ByHalves (F2T :**: F2T) = AlreadyFactors (Factors AtFst (F2T :**: Fls))

instance HasFiniteCovers Overlapping (BOOL, BOOL) where
  covers @a = case obj @a of
    Tru :**: Tru -> [SomeCover ByHalves]
    _ -> []

-- | Gluing for 'Overlapping': a matching family over the two halves agrees on the intersection,
-- and both halves are the same two-valued set, so the value at either leg is the glued one. The
-- smallest instance in which an overlap does any work -- under 'Joins' this same presheaf is
-- no sheaf at all.
instance Sheaf Overlapping Const2 where
  glue ByHalves m = case m AtFst of
    InjL TerminalProfunctor -> InjL TerminalProfunctor
    InjR TerminalProfunctor -> InjR TerminalProfunctor

-- | The kind of finitary presheaves on the two-point space, as a testable kind.
type Sh2 = FINITARY () (BOOL, BOOL)

instance TestableProfunctor (Sub Prof :: CAT Sh2)

instance Testable Sh2 where
  showOb @(SUB p) = show (sizes @p)
  genSome = genSomeDef @'[FIN Sections, FIN Const2, FIN (Yo '(TRU, TRU) (OP '())), FIN (Sieve :: Presheaf (BOOL, BOOL))]

-- | The kind of finitary presheaves on the graph schema, as a testable kind. Needed for the
-- Lawvere--Tierney laws at 'ByEnds', which are stated on the presheaf classifier.
type PshG = FINITARY () GRAPH

instance TestableProfunctor (Sub Prof :: CAT PshG)

instance Testable PshG where
  showOb @(SUB p) = show (sizes @p)
  genSome = genSomeDef @'[FIN TerminalProfunctor, FIN (Yo V (OP '())), FIN (Yo E (OP '())), FIN (Sieve :: Presheaf GRAPH)]

-- | The category of sheaves for 'Overlapping', as a testable kind. The only one of the three
-- whose gluing is an equalizer, so the only one where a quotient of sheaves can have local
-- sections agreeing on the intersection without coming from a global one -- the case
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.factorLocally' descends for. 'Sections' is a sheaf
-- here but has no instance of its own, so it enters tabulated, as at 'ShB'.
type ShO = SHEAVES Overlapping () (BOOL, BOOL)

instance TestableProfunctor (Sub Prof :: CAT ShO)

instance Testable ShO where
  showOb @(SUB p) = show (sizes @p)
  genSome =
    withTabulatedSheaf @Overlapping @Sections
      ( \ @sections _ _ ->
          genSomeList
            "ShO"
            [ Some @(SHF Overlapping Const2)
            , Some @(SHF Overlapping TerminalProfunctor)
            , Some @(SHF Overlapping sections)
            ]
      )
      (error "ShO: Sections is not a sheaf for Overlapping")

-- | The category of sheaves for 'Joins', as a testable kind -- see 'ShB', in particular for why
-- the sheafification is tabulated.
type ShC = SHEAVES Joins () (BOOL, BOOL)

instance TestableProfunctor (Sub Prof :: CAT ShC)

instance Testable ShC where
  showOb @(SUB p) = show (sizes @p)
  genSome =
    withTabulatedSheaf @Joins @(Sheafify Joins Const2)
      ( \ @tab _ _ ->
          genSomeList
            "ShC"
            [Some @(SHF Joins Sections), Some @(SHF Joins TerminalProfunctor), Some @(SHF Joins tab)]
      )
      (error "ShC: the sheafification of Const2 is not a sheaf")

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
    , -- every 'Joins' verdict runs through this numbering, and nothing was checking it
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
        , -- only the maximal sieve is dense, so one plus changes nothing -- for a non-sheaf too
          testPlusFixes @Trivial @Two
        , testPlusFixes @Trivial @Collapse
        ]
    , testGroup
        "Atomic"
        [ testGluesBack @Atomic @Two
        , testLawvereTierney_ @(PROD Sh) (lawvereTierney @Atomic)
        , testProperty "restriction along F2T" $
            for_ ([A', B'] :: [Two FLS '()]) \m ->
              testEq
                "restriction"
                "lmap F2T (glue (Solely F2T) (\\(Only _) -> m))"
                (lmap F2T (glue @Atomic @Two (Solely F2T) \(Only _) -> m))
                "m"
                m
        , testProperty "isSheaf" $ do
            expect "Two is a sheaf" True (isSheaf @Atomic @Two)
            expect "the representable at TRU is a sheaf" True (isSheaf @Atomic @(Yo TRU (OP '())))
            expect "the representable at FLS is not: Atomic is not subcanonical" False (isSheaf @Atomic @(Yo FLS (OP '())))
            -- the counts agree here (2 elements, 2 matching families); only the tables differ
            expect "a collapsing restriction is not a sheaf" False (isSheaf @Atomic @Collapse)
            -- the covariant side is a bystander: the same verdicts two-sidedly
            expect "Yo TRU (OP FLS) is a sheaf" True (isSheaf @Atomic @(Yo TRU (OP FLS) :: BOOL +-> BOOL))
            expect "Yo FLS (OP TRU) is not" False (isSheaf @Atomic @(Yo FLS (OP TRU) :: BOOL +-> BOOL))
        , testGluesBack @Atomic @(Two :*: Two)
        , testProperty "closure under limits" $ do
            expect "a product of sheaves is a sheaf" True (isSheaf @Atomic @(Two :*: Two))
            expect "the terminal profunctor is a sheaf" True (isSheaf @Atomic @(TerminalProfunctor :: Presheaf BOOL))
        , -- at @j = BOOL@, not @j = ()@: over the unit category @'dimap' g h@ collapses to
          -- @'lmap' g@, so a covariant slip in 'closure' would be invisible there
          testProperty "closure is natural" $
            propNaturalTransformation @(Sieve :: BOOL +-> BOOL) (closure @Atomic)
        , testSiteLaws @Atomic @() @BOOL
        , testFinitary @(Plus Atomic Collapse) "Plus Collapse"
        , testFinitary @(Sheafify Atomic Collapse) "Sheafify Collapse"
        , testProfunctor @(Plus Atomic Collapse)
        , testSheafification @Atomic @Collapse @Two
        , -- 'isSheaf' above decides the condition by enumeration; this runs the 'glue' itself
          testGluesBack @Atomic @(Sheafify Atomic Collapse)
        , testGroup
            "the category of sheaves"
            [ testCategory @ShB
            , testTerminalObject @ShB
            , testBinaryProducts_ @ShB
            , testEqualizers_ @ShB
            , testPullbacks_ @ShB
            , -- the colimits, each the presheaf one sheafified
              testInitialObject @ShB
            , testBinaryCoproducts_ @ShB
            , testCoequalizers_ @ShB
            , testPushouts_ @ShB
            , testEpiMonoFactorization_ @ShB
            , -- the exponential is 'FINITARY'\'s, and a sheaf because the codomain is
              testClosed_ @(PROD ShB)
            , testSubobjectClassifier_ @(PROD ShB)
            , testFinitary @(ClosedSieve Atomic :: Presheaf BOOL) "ClosedSieve Atomic"
            , -- 'TRU' is covered by 'FLS', so the sieve that cover generates is dense and its
              -- closure is the maximal one: of the three sieves at 'TRU' only two are closed.
              testProperty "the closed sieves" $ do
                expect "all sieves" [2, 3] (sizes @(Sieve :: Presheaf BOOL))
                expect "closed ones" [2, 2] (sizes @(ClosedSieve Atomic :: Presheaf BOOL))
                expect "and they are a sheaf" True (isSheaf @Atomic @(ClosedSieve Atomic :: Presheaf BOOL))
            , testFinitary @(Sub Prof :: CAT ShB) "ShB"
            , testEqualizersAreSheaves @Atomic @() @BOOL
            ]
        , -- The one cover has no overlaps, so one plus is already a sheaf for /every/ presheaf here:
          -- P⁺(TRU) is the classes of (maximal, x) and ({F2T}, y), identified when x restricts to y,
          -- which is P(FLS) -- and restriction becomes the identity.
          testProperty "one plus suffices without overlaps" $ do
            expect "Plus Collapse is a sheaf" True (isSheaf @Atomic @(Plus Atomic Collapse))
            expect "Plus (Yo FLS) is a sheaf" True (isSheaf @Atomic @(Plus Atomic (Yo FLS (OP '()))))
            expect "Plus (Yo FLS) is the terminal presheaf" [1, 1] (sizes @(Plus Atomic (Yo FLS (OP '()))))
            expect "Sheafify Collapse keeps two elements at each object" [2, 2] (sizes @(Sheafify Atomic Collapse))
            -- and two-sidedly
            expect "Plus (Yo FLS (OP TRU)) is a sheaf" True (isSheaf @Atomic @(Plus Atomic (Yo FLS (OP TRU) :: BOOL +-> BOOL)))
        ]
    , testGroup
        "Overlapping"
        [ -- The same four objects and the same cover as 'Joins', with the empty cover dropped
          -- so that the two legs meet at a section rather than at nothing. This is the only site
          -- here whose gluing is an equalizer instead of a product.
          testProperty "isSheaf" $ do
            expect "the constant presheaf is a sheaf here" True (isSheaf @Overlapping @Const2)
            expect "and is not for Joins, which has an empty cover" False (isSheaf @Joins @Const2)
            expect "Sections is a sheaf too" True (isSheaf @Overlapping @Sections)
        , testProperty "the overlap cuts the pairs down" $ do
            -- four pairs of local sections over the top, of which the two that agree on the
            -- intersection survive; under 'Joins' the intersection is empty and all four do
            expect "sheafified here" [2, 2, 2, 2] (sizes @(Sheafify Overlapping Const2))
            expect "sheafified for Joins" [1, 2, 2, 4] (sizes @(Sheafify Joins Const2))
        , testProperty "the closed sieves are the opens" $
            -- the opens contained in each: the intersection has two, each half three, the union
            -- five -- where 'Joins' sees a discrete pair of points and counts subsets
            expect "Omega" [2, 3, 3, 5] (sizes @(ClosedSieve Overlapping :: Presheaf (BOOL, BOOL)))
        , testLawvereTierney_ @(PROD Sh2) (lawvereTierney @Overlapping)
        , testProperty "closure is natural" $
            propNaturalTransformation @(Sieve :: BOOL +-> (BOOL, BOOL)) (closure @Overlapping)
        , testSiteLaws @Overlapping @() @(BOOL, BOOL)
        , testGluesBack @Overlapping @Const2
        , -- The one place an /exponential/ is glued. Its 'Sheaf' instance searches its elements
          -- for the one that restricts to the family, and no other site here can call it with a
          -- cover whose legs overlap.
          testProperty "the exponential of sheaves is a sheaf" $
            expect "isSheaf" True (isSheaf @Overlapping @(Const2 :~>: Const2))
        , testGluesBack @Overlapping @(Const2 :~>: Const2)
        , -- and the other carrier with no 'glue' of its own: the classifier
          testGluesBack @Overlapping @(ClosedSieve Overlapping :: Presheaf (BOOL, BOOL))
        , -- The presheaf of /all/ sieves is not a sheaf here -- the sixth sieve at the top is not
          -- closed -- and sheafifying it gives the closed ones: the classifier of the sheaves is
          -- the sheafification of the classifier of the presheaves.
          testProperty "sheafifying the sieves gives the closed sieves" $ do
            expect "Sieve is no sheaf here" False (isSheaf @Overlapping @(Sieve :: Presheaf (BOOL, BOOL)))
            expect
              "and its sheafification is Omega"
              (sizes @(ClosedSieve Overlapping :: Presheaf (BOOL, BOOL)))
              (sizes @(Sheafify Overlapping (Sieve :: Presheaf (BOOL, BOOL))))
        , testGroup
            "the category of sheaves"
            [ testCategory @ShO
            , testTerminalObject @ShO
            , testBinaryProducts_ @ShO
            , testEqualizers_ @ShO
            , testPullbacks_ @ShO
            , testInitialObject @ShO
            , testBinaryCoproducts_ @ShO
            , -- No 'testCoequalizers_' (2.6s), no 'testPushouts_' (4.4s) and no
              -- 'testSubobjectClassifier_' (2.9s). The first two reach no branch the cheap groups
              -- here do not -- measured, 'factorLocally' descends at the coproducts above -- and
              -- what is special about quotients here, that a matching pair is a constraint and
              -- not a choice, @Props.Sheaf.Collage@ asserts directly for nothing. The third is
              -- the pushout that epi-mono factorization already drives, and the second runs at
              -- both other sites, with what is special about Omega here -- that it is the five
              -- opens -- asserted directly above at no cost.
              testEpiMonoFactorization_ @ShO
            , testClosed_ @(PROD ShO)
            , testFinitary @(Sub Prof :: CAT ShO) "ShO"
            , testEqualizersAreSheaves @Overlapping @() @(BOOL, BOOL)
            ]
        ]
    , testGroup
        "ByEnds"
        [ -- The one site here that is not a poset: both legs are arrows 'E' -> 'V'. Everything
          -- else in this module runs where a hom-set has at most one arrow, which hides three
          -- things at once -- a sieve cannot tell parallel arrows apart, a factorisation through
          -- a leg cannot be well typed and wrong, and matching collapses to an equation.
          testSiteLaws @ByEnds @() @GRAPH
        , testProperty "sieves tell the two legs apart" $ do
            -- five sieves at 'V': the empty one, 'Src' alone, 'Tgt' alone, both, and everything.
            -- On a poset the two singletons could not both exist. The one that is not closed is
            -- @{Src, Tgt}@, whose closure is the maximal sieve -- that is the cover being a cover.
            expect "all sieves" [2, 5] (sizes @(Sieve :: Presheaf GRAPH))
            expect "closed ones" [2, 4] (sizes @(ClosedSieve ByEnds :: Presheaf GRAPH))
        , testProperty "isSheaf" $ do
            expect "the terminal presheaf is a sheaf" True (isSheaf @ByEnds @(TerminalProfunctor :: Presheaf GRAPH))
            -- not subcanonical, and for a reason the other sites cannot show: a vertex has one
            -- arrow to itself where a sheaf needs one section per pair of ends
            expect "the representable at V is not" False (isSheaf @ByEnds @(Yo V (OP '())))
            expect "nor the one at E" False (isSheaf @ByEnds @(Yo E (OP '())))
        , testProperty "sheafifying makes the vertices the pairs of ends" $ do
            expect "before" [2, 1] (sizes @(Yo V (OP '())))
            expect "after" [2, 4] (sizes @(Sheafify ByEnds (Yo V (OP '()))))
        , -- which covers "is a sheaf" as one of its four, and the reflector's laws besides
          testSheafification @ByEnds @(Yo V (OP '())) @(TerminalProfunctor :: Presheaf GRAPH)
        , testLawvereTierney_ @(PROD PshG) (lawvereTierney @ByEnds)
        , testProperty "closure is natural" $ propNaturalTransformation @(Sieve :: Presheaf GRAPH) (closure @ByEnds)
        ]
    , testGroup
        "Joins"
        [ testGluesBack @Joins @Sections
        , testLawvereTierney_ @(PROD Sh2) (lawvereTierney @Joins)
        , testProperty "isSheaf" $ do
            expect "Sections is a sheaf" True (isSheaf @Joins @Sections)
            expect "the constant presheaf is not: two sections over the empty set" False (isSheaf @Joins @Const2)
            sequence_
              ( foreachOb @(BOOL, BOOL) @(Property ()) \ @a ->
                  [ expect
                      ("the representable at object " ++ show (objIndex @a) ++ " is a sheaf: Joins is subcanonical")
                      True
                      (isSheaf @Joins @(Yo a (OP '())))
                  ]
              )
            -- subcanonical is about the representable presheaves: two-sidedly the empty cover bites,
            -- since TRU has no arrow to FLS and so no section over the empty set there
            expect
              "the two-sided representable at '(TRU, FLS) over TRU is not a sheaf"
              False
              (isSheaf @Joins @(Yo '(TRU, FLS) (OP TRU) :: BOOL +-> (BOOL, BOOL)))
        , testProperty "closure is natural" $
            propNaturalTransformation @(Sieve :: BOOL +-> (BOOL, BOOL)) (closure @Joins)
        , testGluesBack @Joins @(ClosedSieve Joins :: Presheaf (BOOL, BOOL))
        , testSiteLaws @Joins @() @(BOOL, BOOL)
        , testFinitary @(Plus Joins Const2) "Plus Const2"
        , testFinitary @(Sheafify Joins Const2) "Sheafify Const2"
        , testSheafification @Joins @Const2 @Sections
        , testGluesBack @Joins @(Sheafify Joins Const2)
        , testGroup
            "the category of sheaves"
            [ testCategory @ShC
            , testTerminalObject @ShC
            , testBinaryProducts_ @ShC
            , testEqualizers_ @ShC
            , testPullbacks_ @ShC
            , testInitialObject @ShC
            , testBinaryCoproducts_ @ShC
            , testCoequalizers_ @ShC
            , -- No 'testPushouts_' here: the apex is the sheafified coproduct, whose sections over
              -- the whole space are the pairs, and the law draws three arrows out of it -- each an
              -- enumeration over 15 points where a coequalizer's is over 6 (4.2s for the group).
              -- Epi-mono factorization covers the same pushout at a quarter the cost.
              testEpiMonoFactorization_ @ShC
            , testClosed_ @(PROD ShC)
            , testSubobjectClassifier_ @(PROD ShC)
            , testFinitary @(ClosedSieve Joins :: Presheaf (BOOL, BOOL)) "ClosedSieve Joins"
            , -- The closed sieves on a space are its opens: over the empty set only the empty one,
              -- where the presheaf of all sieves has two, and the four subsets over the whole.
              testProperty "the closed sieves are the opens" $ do
                expect "all sieves" [2, 3, 3, 6] (sizes @(Sieve :: Presheaf (BOOL, BOOL)))
                expect "closed ones" [1, 2, 2, 4] (sizes @(ClosedSieve Joins :: Presheaf (BOOL, BOOL)))
                expect
                  "and they are a sheaf"
                  True
                  (isSheaf @Joins @(ClosedSieve Joins :: Presheaf (BOOL, BOOL)))
            , testFinitary @(Sub Prof :: CAT ShC) "ShC"
            , testEqualizersAreSheaves @Joins @() @(BOOL, BOOL)
            ]
        , -- Every sieve at the empty set is dense, and the empty sieve is the meet of them all, so
          -- one plus leaves 'Const2' a single section over the empty set. But the whole space still
          -- has two, where a sheaf now needs a section per pair over the two points: four. The
          -- second plus supplies them, and the result is the constant sheaf with fibre two.
          testProperty "two pluses are needed" $ do
            expect "one plus: one section over the empty set" [1, 2, 2, 2] (sizes @(Plus Joins Const2))
            expect "one plus is not yet a sheaf" False (isSheaf @Joins @(Plus Joins Const2))
            expect "two pluses: the constant sheaf" [1, 2, 2, 4] (sizes @(Sheafify Joins Const2))
        , -- the presentation that 'ShC' draws from is the same sheaf
          withTabulatedSheaf @Joins @(Sheafify Joins Const2)
            ( \ @tab _ _ ->
                testGroup
                  "the tabulated sheafification"
                  [ testProperty "is the same sheaf" $ do
                      expect "has the sheafification's sizes" [1, 2, 2, 4] (sizes @tab)
                      expect "is a sheaf" True (isSheaf @Joins @tab)
                  , -- a 'Tabulated' glues by search; this is the law that search has to satisfy
                    testGluesBack @Joins @tab
                  ]
            )
            (error "the tabulated sheafification is not a sheaf")
        ]
    ]
