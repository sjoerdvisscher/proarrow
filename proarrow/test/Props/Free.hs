{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Free where

import Control.Applicative (Alternative (..))
import Control.Monad (unless)
import Data.Foldable (for_)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat2)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude hiding (Monoid, curry, fst, id, mempty, snd, (**), (.))
import Prelude qualified as P

import Proarrow.Category.Instance.FinRel (FINREL (..))
import Proarrow.Category.Instance.Free (FREE (..), Free (..), Lower, retract, widen)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..), SymMonoidal, UnitF, withOb2, type (**!))
import Proarrow.Category.Monoidal.Cartesian (Cartesian, prodToTensor, tensorToProd, termToUnit, unitToTerm)
import Proarrow.Category.Monoidal.Closed (Closed, apply, curry, withObExp, type (-->))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed)
import Proarrow.Category.Monoidal.Distributive (Distributive)
import Proarrow.Category.Monoidal.StarAutonomous (DualF, StarAutonomous)
import Proarrow.Category.Sheaf (Cover (..), Leg (..), Sheaf (..), Summands, Sums, legArrow)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), type (+))
import Proarrow.Colimit.Initial (HasInitialObject (..), InitF)
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), lmap, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..), type (@))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), type (*!))
import Proarrow.Limit.Terminal (HasTerminalObject (..), TermF)
import Proarrow.Monoid (Comonoid (..), Monoid (..), Supplies)
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))
import Proarrow.Profunctor.Representable (Rep (..))

import Proarrow.Testing
  ( GenTotal (..)
  , MkSomeList (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genNamed
  , genSomeDef
  , oneOfTotal
  , testEq
  )
import Proarrow.Testing.Laws
import Props.Hask ()

type FREECS =
  '[ HasInitialObject
   , HasTerminalObject
   , HasBinaryProducts
   , HasBinaryCoproducts
   , Monoidal
   , SymMonoidal
   , Closed
   , Distributive
   , StarAutonomous
   , CompactClosed
   , Supplies Monoid
   , Supplies Comonoid
   ]
type FREEKIND = FREE FREECS (InitialProfunctor :: CAT ())

-- | The free category has no generating morphisms to interpret (@'InitialProfunctor'@ is
-- uninhabited), so any object at all works as the interpretation of @'()@. A small finite set
-- gives 'retract' below plenty to sample from. It is in 'FINREL', not 'Type', since
-- 'StarAutonomous'\/'CompactClosed' need a target that has dual objects.
data family Interp :: () +-> FINREL

instance FunctorForRep Interp where
  type Interp @ '() = FR Nat2
  fmap Unit = obj @(FR Nat2)

-- | The object @a@ interpreted in 'FINREL', by folding its structure through 'Interp'.
type LowerT a = Lower (Rep Interp) a

test :: TestTree
test =
  testGroup
    "Free"
    [ testCategory @FREEKIND
    , testTerminalObject @FREEKIND
    , testInitialObject @FREEKIND
    , testBinaryProducts @FREEKIND (\ @a @b r -> withObProd @FINREL @(LowerT a) @(LowerT b) r)
    , testBinaryCoproducts @FREEKIND (\ @a @b r -> withObCoprod @FINREL @(LowerT a) @(LowerT b) r)
    , testClosed @FREEKIND
        (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
        (\ @a @b r -> withObExp @FINREL @(LowerT a) @(LowerT b) r)
    , testMonoidal @FREEKIND (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
    , testSymMonoidal @FREEKIND (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
    , testDistributive @FREEKIND
        (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
        (\ @a @b r -> withObCoprod @FINREL @(LowerT a) @(LowerT b) r)
    , -- 'testStarAutonomous' isn't wired in here. Its naturality checks need e.g. an arbitrary
      -- @a ** b ~> Dual c@ for independently-drawn a,b,c, but in a free category that hom-set is
      -- empty for most palette triples (no unitor/associator-driven bridge connects a plain
      -- tensor shape to an unrelated dualized one). 'genTerm' can't conjure a morphism that
      -- doesn't exist, so every sample gets discarded. 'testCompactClosed' avoids this, since none
      -- of its checks need to generate a random Dual-involving morphism, only compose the fixed
      -- ones 'CompactClosed' already provides.
      testCompactClosed @FREEKIND
        (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
        (\ @a @b r -> withObExp @FINREL @(LowerT a) @(LowerT b) r)
        (\r -> r)
    , testHypergraph @FREEKIND (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
    , sheafTests
    , testProperty "cartesian coercions interpret to identities" P.$ do
        let roundTrip = retract @CARTCS @(Rep InterpT) (tensorToProd @(EMB '()) @(EMB '()) . prodToTensor @(EMB '()) @(EMB '()))
            unitTrip = retract @CARTCS @(Rep InterpT) (unitToTerm . termToUnit)
        unless (roundTrip (True, False) P.== (True, False) P.&& unitTrip () P.== ()) (testFailed "cartesian coercions")
    , testProperty "retract . widen = retract" P.$ do
        let l = retract @NARROWCS @(Rep Interp) narrowTerm
            r = retract @FREECS @(Rep Interp) (widen @FREECS narrowTerm)
        unless (l P.== r) (testFailed (P.show l P.++ " /= " P.++ P.show r))
    ]

-- * The cartesian coercions

-- | A free category with the 'Cartesian' marker, interpreted into @Type@ (where the coercions
-- are identities), with the one generator object standing for 'Bool'.
type CARTCS = '[Cartesian, HasTerminalObject, HasBinaryProducts, Monoidal]

data family InterpT :: () +-> Type

instance FunctorForRep InterpT where
  type InterpT @ '() = Bool
  fmap Unit = obj @Bool

-- * Widening

type NARROWCS = '[HasInitialObject, HasTerminalObject, HasBinaryProducts]

-- | A term using all three structures of the narrow list, for the widening test above.
narrowTerm
  :: Free
       ((InitF *! TermF) :: FREE NARROWCS (InitialProfunctor :: CAT ()))
       ((TermF *! InitF) *! TermF)
narrowTerm = (terminate &&& (initiate @_ @InitF . fst @_ @InitF @TermF)) &&& snd @_ @InitF @TermF

-- | A singleton witnessing the shape of an object expression, so 'genTerm' can pattern-match
-- on source and target shapes directly instead of needing a type class per shape.
data SFree (a :: FREEKIND) where
  SInit :: SFree InitF
  STerm :: SFree TermF
  SProd :: (Ob a, Ob b) => SFree a -> SFree b -> SFree (a *! b)
  SSum :: (Ob a, Ob b) => SFree a -> SFree b -> SFree (a + b)
  SUnit :: SFree UnitF
  STen :: (Ob a, Ob b) => SFree a -> SFree b -> SFree (a **! b)
  SExp :: (Ob a, Ob b) => SFree a -> SFree b -> SFree (a --> b)
  SDual :: (Ob a) => SFree a -> SFree (DualF a)

class (Ob a) => KnownFree (a :: FREEKIND) where
  theFree :: SFree a
instance KnownFree InitF where
  theFree = SInit
instance KnownFree TermF where
  theFree = STerm
instance (KnownFree a, KnownFree b) => KnownFree (a *! b) where
  theFree = SProd theFree theFree
instance (KnownFree a, KnownFree b) => KnownFree (a + b) where
  theFree = SSum theFree theFree
instance KnownFree UnitF where
  theFree = SUnit
instance (KnownFree a, KnownFree b) => KnownFree (a **! b) where
  theFree = STen theFree theFree
instance (KnownFree a, KnownFree b) => KnownFree (a --> b) where
  theFree = SExp theFree theFree
instance (KnownFree a) => KnownFree (DualF a) where
  theFree = SDual theFree

-- | Decides whether two object shapes are the same, structurally. 'genTerm' uses this to
-- check whether a generator branch's source\/target lines up with the shape it wants
-- to produce, without needing runtime type reflection.
eqSFree :: SFree a -> SFree b -> Maybe (a :~: b)
eqSFree SInit SInit = Just Refl
eqSFree STerm STerm = Just Refl
eqSFree (SProd a1 a2) (SProd b1 b2) = case (eqSFree a1 b1, eqSFree a2 b2) of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
eqSFree (SSum a1 a2) (SSum b1 b2) = case (eqSFree a1 b1, eqSFree a2 b2) of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
eqSFree SUnit SUnit = Just Refl
eqSFree (STen a1 a2) (STen b1 b2) = case (eqSFree a1 b1, eqSFree a2 b2) of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
eqSFree (SExp a1 a2) (SExp b1 b2) = case (eqSFree a1 b1, eqSFree a2 b2) of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
eqSFree (SDual a1) (SDual b1) = case eqSFree a1 b1 of
  Just Refl -> Just Refl
  Nothing -> Nothing
eqSFree _ _ = Nothing

-- | Render an object shape for test failure output.
showSFree :: SFree a -> String
showSFree SInit = "InitF"
showSFree STerm = "TermF"
showSFree (SProd a b) = "(" ++ showSFree a ++ " *! " ++ showSFree b ++ ")"
showSFree (SSum a b) = "(" ++ showSFree a ++ " + " ++ showSFree b ++ ")"
showSFree SUnit = "UnitF"
showSFree (STen a b) = "(" ++ showSFree a ++ " **! " ++ showSFree b ++ ")"
showSFree (SExp a b) = "(" ++ showSFree a ++ " --> " ++ showSFree b ++ ")"
showSFree (SDual a) = "(Dual " ++ showSFree a ++ ")"

-- | The finite palette of shapes 'Testable' picks 'Some' objects from as the /endpoints/ of a
-- generated term. @composeB@ routes through 'Intermediates'.
--
-- Every shape is built from 'UnitF', and none from 'TermF' or 'InitF'. Terms are compared by
-- interpretation into 'FINREL', where the terminal and initial objects are both the empty set, so
-- at any object built from them alone every hom-set has one element and every comparison is
-- vacuous. The unit interprets to a one-element set, and the shapes over it do not collapse.
type Palette = '[UnitF, UnitF *! UnitF, UnitF + UnitF, UnitF **! UnitF, UnitF --> UnitF]

-- | The shapes @composeB@ routes intermediates through. It is 'Palette' plus 'TermF' and 'InitF'.
-- As /endpoints/ those two are useless (every hom-set at them is a singleton in 'FINREL', so a
-- comparison there cannot fail), but as /waypoints/ they are not. Going through 'TermF' builds
-- @'counit' '.' 'terminate' :: 'UnitF' '~>' 'UnitF'@, which interprets to the empty relation and is
-- the only non-identity endomorphism of 'UnitF' the generator can reach. Without it every law
-- comparison landing at @'UnitF' '~>' 'UnitF'@ is a single fixed instance.
type Intermediates = TermF ': InitF ': Palette

intermediates :: [Some FREEKIND]
intermediates = mkSomeList @FREEKIND @Intermediates

-- | Generate a random term between two (given) object shapes. Most branches recurse
-- structurally on a strictly smaller sub-shape of the source or target, so they always
-- terminate on their own; @composeB@ is the exception (it can reach into an unrelated object
-- via composition), so it's the one branch bounded by @fuel@, which decreases on every
-- recursive call and cuts it off at zero.
genTerm :: forall a b. (Ob a, Ob b) => Int -> SFree a -> SFree b -> GenTotal (Free a b)
genTerm fuel sa sb =
  oneOfTotal [idB, initiateB, terminateB, unitB, counitB, fstSndB, applyB, recB]
  where
    recB
      | fuel <= 0 = empty
      | otherwise = oneOfTotal [prodB, tensorB, sumSrcB, sumTgtB, curryB, composeB]
    idB = case eqSFree sa sb of
      Just Refl -> pure id
      Nothing -> empty
    initiateB = case sa of
      SInit -> pure initiate
      _ -> empty
    terminateB = case sb of
      STerm -> pure terminate
      _ -> empty
    -- The unit is neither initial nor terminal, but every object is a monoid and a comonoid here,
    -- so there is a canonical arrow from it and one to it all the same.
    unitB = case sa of
      SUnit -> pure mempty
      _ -> empty
    counitB = case sb of
      SUnit -> pure counit
      _ -> empty
    fstSndB = case sa of
      SProd sa1 sa2 ->
        oneOfTotal
          [ case eqSFree sb sa1 of Just Refl -> pure fst; Nothing -> empty
          , case eqSFree sb sa2 of Just Refl -> pure snd; Nothing -> empty
          ]
      _ -> empty
    prodB = case sb of
      SProd b1 b2 -> (&&&) <$> genTerm (fuel - 1) sa b1 <*> genTerm (fuel - 1) sa b2
      _ -> empty
    tensorB = case (sa, sb) of
      (STen a1 a2, STen b1 b2) -> (**) <$> genTerm (fuel - 1) a1 b1 <*> genTerm (fuel - 1) a2 b2
      _ -> empty
    sumSrcB = case sa of
      SSum a1 a2 -> (|||) <$> genTerm (fuel - 1) a1 sb <*> genTerm (fuel - 1) a2 sb
      _ -> empty
    sumTgtB = case sb of
      SSum b1 b2 -> oneOfTotal [(lft .) <$> genTerm (fuel - 1) sa b1, (rgt .) <$> genTerm (fuel - 1) sa b2]
      _ -> empty
    -- a ~ (b --> c) **! b, with c ~ the target.
    applyB = case sa of
      STen sl sr -> case sl of
        SExp sea1 sea2 -> case (eqSFree sr sea1, eqSFree sb sea2) of
          (Just Refl, Just Refl) -> pure apply
          _ -> empty
        _ -> empty
      _ -> empty
    curryB = case sb of
      SExp b1 b2 -> curry <$> genTerm (fuel - 1) (STen sa b1) b2
      _ -> empty
    -- Route through every palette shape as a possible intermediate object. Without this the
    -- generator could never compose two otherwise-unrelated terms.
    composeB =
      oneOfTotal
        [ (.) <$> genTerm (fuel - 1) (theFree @mid) sb <*> genTerm (fuel - 1) sa (theFree @mid)
        | Some @mid <- intermediates
        ]

-- | Bridges straight to 'FINREL'\'s 'Ob' instead of its 'TestOb'. 'Testable FINREL' leaves
-- 'TestOb' at its class default ('type TestOb a = Ob a'), and an unrestated default associated
-- type equation doesn't get unfolded through an abstract type variable the way an explicit
-- instance override (like 'CategoryOf FINREL'\'s own 'Ob' equation) does.
instance Testable FREEKIND where
  type TestOb a = (KnownFree a, Ob (LowerT a))
  showOb @a = showSFree (theFree @a)
  genSome = genSomeDef @Palette

-- | Two terms are equal iff they denote the same relation once interpreted into 'FINREL' via
-- 'retract', decided by 'FinRel'\'s own 'Eq'. Structural equality on 'Free' terms would be too
-- strict for testing categorical laws: e.g. @'terminate' . f@ and @'terminate'@ are built from
-- different 'Free' constructors even though uniqueness of the terminal object makes them denote
-- the same morphism.
instance (TestOb a, TestOb b) => TestingEqShow (Free (a :: FREEKIND) b) where
  eqP l r = pure (retract @FREECS @(Rep Interp) l == retract @FREECS @(Rep Interp) r)

instance (TestOb a, TestOb b) => TestableType (Free (a :: FREEKIND) b) where
  gen = genTerm 3 (theFree @a) (theFree @b)
instance TestableProfunctor (Free :: CAT FREEKIND)

-- | The cover of the booleans by their two points. 'BySummands' is polymorphic in the summands, so
-- the cover it is used at has to be pinned. The summands are 'UnitF' and not @TermF@ for the reason
-- 'Palette' gives.
boolCover :: Cover Sums FREEKIND (UnitF + UnitF) (Summands (UnitF :: FREEKIND) UnitF)
boolCover = BySummands

-- | The sum coverage on the free category, at the cover of the booleans by their two points: the
-- representables glue by @'|||'@. So restriction along either injection gives the branch back, and
-- an element is the gluing of its restrictions.
sheafTests :: TestTree
sheafTests =
  testGroup
    "Sums"
    [ testGluesBackAt @Sums @(Yo (UnitF + UnitF) (OP '())) "BySummands, sum representable" boolCover
    , -- the two-sided representable's own profunctor laws. These exercise 'Yo'\'s action on the
      -- covariant component, which the presheaf cases above leave at the identity
      testProfunctor @(Yo (UnitF + UnitF) (OP Bool) :: Type +-> FREEKIND)
    , testGluesBackAt
        @Sums
        @(Yo (UnitF + UnitF) (OP Bool) :: Type +-> FREEKIND)
        "BySummands, representable over Hask"
        boolCover
    , -- The gluing keeps one covariant component where the family supplies two, so it is only well
      -- The gluing keeps one covariant component of the two the family supplies, which is well
      -- defined because the two agree on the overlap. After restricting along the overlap the
      -- contravariant components are always equal ('InitF' is initial), so the covariant ones
      -- decide. The un-restricted pair below is the other way round, so both halves of 'eqP' on
      -- 'Yo' are exercised.
      testProperty "the overlap decides the covariant component" do
        let overlap = initiate @FREEKIND @UnitF
            at
              :: Free (UnitF :: FREEKIND) (UnitF + UnitF) -> (Bool -> Bool) -> Yo (UnitF + UnitF) (OP Bool) (UnitF :: FREEKIND) Bool
            at inj h = Yo inj h
        for_ [(h, h') | h <- [P.id, P.not], h' <- [P.id, P.not]] \(h, h') -> do
          agree <- eqP h h'
          same <- eqP (lmap overlap (at lft h)) (lmap overlap (at rgt h'))
          expect "restricted to the overlap: equal exactly when the covariant halves agree" agree same
          apart <- eqP (at lft h) (at rgt h)
          expect "un-restricted: the differing contravariant halves separate them" False apart
    , -- The commuting conversion, in sheaf vocabulary: a map of sheaves carries a gluing to the
      -- gluing of the mapped family. At the representable, gluing is @'|||'@ and the map is
      -- post-composition, so this is @h '.' (t '|||' e) = (h '.' t) '|||' (h '.' e)@, the
      -- equation that makes @f (if b then x else y)@ and @if b then f x else f y@ the same
      -- program. It follows from restriction and uniqueness together with @h@\'s naturality, so it
      -- is not a new law but a demonstration.
      testProperty "a map of sheaves commutes with the gluing" do
        t <- genNamed @(Free (UnitF :: FREEKIND) (UnitF + UnitF)) "t"
        e <- genNamed @(Free (UnitF :: FREEKIND) (UnitF + UnitF)) "e"
        -- @h@ has to land somewhere it can be injective. Every term @(UnitF + UnitF) ~> UnitF@ the
        -- generator can build collapses the two summands, and then @h . t = h . e@ for almost any
        -- branches and the equation holds for the wrong reason.
        h <- genNamed @(Free ((UnitF :: FREEKIND) + UnitF) (UnitF + UnitF)) "h"
        let after
              :: Yo ((UnitF :: FREEKIND) + UnitF) (OP '()) z '()
              -> Yo ((UnitF :: FREEKIND) + UnitF) (OP '()) z '()
            after (Yo f g) = Yo (h . f) g
            fam
              :: forall z
               . Leg Sums FREEKIND (UnitF + UnitF) (Summands (UnitF :: FREEKIND) UnitF) z
              -> Yo ((UnitF :: FREEKIND) + UnitF) (OP '()) z '()
            fam AtLeft = Yo t Unit
            fam AtRight = Yo e Unit
        testEq
          "commuting conversion"
          "h . glue [t, e]"
          (after (glue @Sums boolCover fam))
          "glue [h . t, h . e]"
          (glue @Sums boolCover (\g -> after (fam g)))
    , testProperty "restriction at BySummands" do
        t <- genNamed @(Free UnitF (UnitF + UnitF)) "t"
        e <- genNamed @(Free UnitF (UnitF + UnitF)) "e"
        let ite = glue @Sums @(Yo (UnitF + UnitF) (OP '())) boolCover \case
              AtLeft -> Yo t Unit
              AtRight -> Yo e Unit
        testEq "then" "lmap lft (glue [t, e])" (lmap (legArrow AtLeft) ite) "t" (Yo t Unit)
        testEq "else" "lmap rgt (glue [t, e])" (lmap (legArrow AtRight) ite) "e" (Yo e Unit)
    ]
