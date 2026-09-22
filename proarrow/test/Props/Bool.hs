{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Bool where

import Data.Type.Equality ((:~:) (Refl))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (discard, testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Enriched qualified as E
import Proarrow.Category.Enriched.Thin (HasArrow, Holds, Objects, ThinProfunctor (..))
import Proarrow.Category.Enriched.Thin.Composition (Closure)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), NonTrivialProfunctor (..))
import Proarrow.Category.Instance.Collage (COLLAGE (..), Collage)
import Proarrow.Category.Instance.Opposite (Op)
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (CAT, Ob, Promonad (..), obj, rmap, type (+->), type (~>))
import Proarrow.Profunctor.Corepresentable (Corep)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Direp (Direp)
import Proarrow.Profunctor.Instance.Exponential ((:~>:))
import Proarrow.Profunctor.Instance.Product ((:*:))
import Proarrow.Profunctor.Representable (CorepStar, Rep)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Testing
  ( GenTotal (..)
  , Some (..)
  , SomeProfunctorElt (..)
  , Testable (..)
  , TestableProfunctor (..)
  , TestableType (..)
  , TestingEqShow (..)
  , genNamed
  , genObSuchThat
  , genSomeFinite
  , isGenNonEmpty
  , oneElem
  , someElemNamed
  , testEq
  )
import Proarrow.Testing.Laws

test :: TestTree
test =
  testGroup
    "Booleans"
    [ testCategory @BOOL
    , testTerminalObject @BOOL
    , testInitialObject @BOOL
    , testBinaryProducts_ @BOOL
    , testCartesian_ @BOOL
    , testMonoidal_ @BOOL
    , testMonoidalHom_ @BOOL
    , testSymMonoidal_ @BOOL
    , testCopyDiscard_ @BOOL
    , testStarAutonomous_ @BOOL
    , testBinaryCoproducts_ @BOOL
    , testDistributive_ @BOOL
    , testClosed_ @BOOL
    , testEqualizers_ @BOOL
    , testCoequalizers_ @BOOL
    , testPullbacks_ @BOOL
    , testPushouts_ @BOOL
    , testCommutativeMonoid_ @TRU
    , testProperty "FF,FT profunctor" $ propProfunctor @(NonTrivialProfunctor '(TRU, FLS))
    , testProperty "FT,TT profunctor" $ propProfunctor @(NonTrivialProfunctor '(FLS, TRU))
    , testProperty "FF,FT,TT profunctor" $ propProfunctor @(NonTrivialProfunctor '(TRU, TRU))
    , testProperty "Booleans decidable" $ propDecidable @Booleans
    , testProperty "FF,FT decidable" $ propDecidable @(NonTrivialProfunctor '(TRU, FLS))
    , testProperty "FT,TT decidable" $ propDecidable @(NonTrivialProfunctor '(FLS, TRU))
    , testProperty "Op Booleans decidable" $ propDecidable @(Op Booleans)
    , testProperty "reachability finds a path" $ withArr reachPath (pure ())
    , testProperty "Booleans is BOOL-enriched" $ do
        SomeP @a @b p <- genProfunctorElt @Booleans "p"
        testEq "enriched . underlying" "enriched (underlying p)" (E.enriched @BOOL (E.underlying @BOOL p)) "p" p
        Some @c <- genObSuchThat @BOOL \(Some @c) -> isGenNonEmpty @(b ~> c)
        g <- genNamed @(b ~> c) "g"
        testEq
          "rmap"
          "enriched (rmap . (underlying g ** underlying p))"
          (E.enriched @BOOL @Booleans (E.rmap @BOOL @Booleans @a @b @c . (E.underlying @BOOL g ** E.underlying @BOOL p)))
          "rmap g p"
          (rmap g p)
    , testProperty "thin composition round trips through withArr" $
        withArr compLeft $
          withArr compRight $
            withArr compRightCorepStar $
              withArr compSearch $
                withArr compSearch3 (pure ())
    ]

-- * Composition of thin profunctors, checked at the type level

-- | Coherence law: a corepresented left leg followed by a represented right leg is 'Direp' --
-- both constraints reduce to @f a ≤ g c@, so the identity typechecks in either direction.
compIsDirep
  :: forall {i} {j} {k} (f :: j +-> k) (g :: i +-> k) (a :: j) (c :: i) r
   . ((HasArrow (Direp f g) a c) => r) -> ((HasArrow (Corep f :.: Rep g) a c) => r)
compIsDirep r = r

direpIsComp
  :: forall {i} {j} {k} (f :: j +-> k) (g :: i +-> k) (a :: j) (c :: i) r
   . ((HasArrow (Corep f :.: Rep g) a c) => r) -> ((HasArrow (Direp f g) a c) => r)
direpIsComp r = r

-- | On the walking arrow: a constant-@FLS@ left leg substitutes @FLS@ for the middle object,
-- and @FLS ≤ FLS@ holds, so the composite arrow exists (this only typechecks because it does).
compLeft :: (Corep (Constant FLS) :.: Booleans) TRU FLS
compLeft = arr

-- | Dually, a constant-@TRU@ right leg substitutes @TRU@: @FLS ≤ TRU@.
compRight :: (Booleans :.: Rep (Constant TRU)) FLS FLS
compRight = arr

-- | The same substitution through a corepresentable profunctor's 'CorepStar'.
compRightCorepStar :: (Booleans :.: CorepStar (Corep (Constant TRU))) FLS FLS
compRightCorepStar = arr

-- | Two non-representable legs: the middle object is found by searching @BOOL@. Here @FLS@ reaches
-- @TRU@ through either middle object, and only the search can tell.
compSearch :: (NonTrivialProfunctor '(TRU, FLS) :.: NonTrivialProfunctor '(FLS, TRU)) FLS TRU
compSearch = arr

-- | Searches nest: a composite is decidable again, so it can be the leg of a further search.
compSearch3 :: ((NonTrivialProfunctor '(TRU, FLS) :.: NonTrivialProfunctor '(FLS, TRU)) :.: Booleans) FLS TRU
compSearch3 = arr

-- | A failed search is a type-level fact too: the first leg only leaves @TRU@ at @TRU@, where the
-- second leg has nothing, so the composite has no arrow out of @TRU@.
searchMisses :: Holds (NonTrivialProfunctor '(FLS, TRU) :.: NonTrivialProfunctor '(TRU, FLS)) TRU FLS :~: FLS
searchMisses = Refl

searchHits :: Holds (NonTrivialProfunctor '(TRU, FLS) :.: NonTrivialProfunctor '(FLS, TRU)) FLS TRU :~: TRU
searchHits = Refl

-- | The exponential of profunctors is implication: it fails exactly where the antecedent holds and
-- the consequent does not.
exponentialMisses :: Holds (Booleans :~>: NonTrivialProfunctor '(FLS, TRU)) FLS FLS :~: FLS
exponentialMisses = Refl

exponentialHits :: Holds (NonTrivialProfunctor '(FLS, TRU) :~>: Booleans) FLS FLS :~: TRU
exponentialHits = Refl

-- | Decidability is structural: a product of profunctors holds when both do.
productMisses :: Holds (Booleans :*: NonTrivialProfunctor '(FLS, TRU)) FLS FLS :~: FLS
productMisses = Refl

instance Testable BOOL where
  showOb @a = case obj @a of
    Fls -> "FLS"
    Tru -> "TRU"
  genSome = genSomeFinite

instance (Ob a, Ob b) => TestableType (Booleans a b) where
  gen = case (obj @a, obj @b) of
    (Fls, Fls) -> oneElem Fls
    (Fls, Tru) -> oneElem F2T
    (Tru, Tru) -> oneElem Tru
    (Tru, Fls) -> GenEmpty \case {}
instance (Ob a, Ob b) => TestingEqShow (Booleans a b) where
  -- thin, so parallel arrows are equal for free; forcing is the one thing left to check
  eqP l r = l `seq` r `seq` pure True
  showP Fls = "F->F"
  showP F2T = "F->T"
  showP Tru = "T->T"
instance TestableProfunctor Booleans

instance (Ob ft) => TestableProfunctor (NonTrivialProfunctor ft) where
  genProfunctorElt nm = case obj @ft of
    Tru :**: Fls -> someElemNamed nm [SomeP FF, SomeP FT]
    Tru :**: Tru -> someElemNamed nm [SomeP FF, SomeP FT, SomeP TT]
    Fls :**: Tru -> someElemNamed nm [SomeP FT, SomeP TT]
    Fls :**: Fls -> discard
instance (Ob ft, TestOb a, TestOb b) => TestingEqShow (NonTrivialProfunctor ft a b)
instance (Ob ft, TestOb a, TestOb b) => TestableType (NonTrivialProfunctor ft a b) where
  gen = case (obj @ft, obj @a, obj @b) of
    (Tru :**: _, Fls, Fls) -> oneElem FF
    (Fls :**: _, Fls, Fls) -> GenEmpty \case {}
    (_, Fls, Tru) -> oneElem FT
    (_ :**: Tru, Tru, Tru) -> oneElem TT
    (_ :**: Fls, Tru, Tru) -> GenEmpty \case {}
    (_, Tru, Fls) -> GenEmpty \case {}

-- | The same closure at the value level: 'Closure' is decidable, and 'arr' searches the path.
reachPath :: Closure (NonTrivialProfunctor '(FLS, FLS)) FLS TRU
reachPath = arr

reachNoPath :: Holds (Closure (NonTrivialProfunctor '(FLS, FLS))) TRU FLS :~: FLS
reachNoPath = Refl

-- * The collage of a profunctor is enumerable

-- | Two copies of the walking arrow, glued by the profunctor that only relates @FLS@ to @TRU@.
type Glued = COLLAGE (NonTrivialProfunctor '(FLS, FLS))

-- | The left category's objects are numbered first, the right's after them.
objectsGlued :: Objects Glued :~: '[L FLS, L TRU, R FLS, R TRU]
objectsGlued = Refl

-- | The closure reaches across the glue, by the one heteromorphism.
gluedAcross :: Holds (Closure (Collage :: CAT Glued)) (L FLS) (R TRU) :~: TRU
gluedAcross = Refl

-- | It does not reach the right object the profunctor misses, even going the long way round.
gluedMisses :: Holds (Closure (Collage :: CAT Glued)) (L FLS) (R FLS) :~: FLS
gluedMisses = Refl

-- | And never back across the glue.
gluedNoWayBack :: Holds (Closure (Collage :: CAT Glued)) (R TRU) (L FLS) :~: FLS
gluedNoWayBack = Refl
