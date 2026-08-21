{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Free where

import Control.Applicative (Alternative (..))
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat2)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (curry, fst, id, snd, (.))

import Proarrow.Category.Instance.FinRel (FINREL (..))
import Proarrow.Category.Instance.Free (FREE (..), Free (..), IsFreeOb (..), retract)
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal (Monoidal, SymMonoidal, UnitF, withOb2, type (**!))
import Proarrow.Category.Monoidal.Closed (Closed, apply, curry, withObExp, type (-->))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed)
import Proarrow.Category.Monoidal.StarAutonomous (DualF, StarAutonomous)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), type (+))
import Proarrow.Colimit.Initial (HasInitialObject (..), InitF)
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), obj, type (+->))
import Proarrow.Functor (FunctorForRep (..), type (@))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), type (*!))
import Proarrow.Limit.Terminal (HasTerminalObject (..), TermF)
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Representable (Rep (..))

import Props
import Props.Hask ()
import Testable
  ( GenTotal (..)
  , MkSomeList (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , oneOfTotal
  )

type FREECS =
  '[ HasInitialObject
   , HasTerminalObject
   , HasBinaryProducts
   , HasBinaryCoproducts
   , Monoidal
   , SymMonoidal
   , Closed
   , StarAutonomous
   , CompactClosed
   ]
type FREEKIND = FREE FREECS (InitialProfunctor :: CAT ())

-- | The free category has no generating morphisms to interpret (@'InitialProfunctor'@ is
-- uninhabited), so any object at all works as the interpretation of @'()@ — a small finite set
-- ('FINREL', rather than 'Type', since 'StarAutonomous'\/'CompactClosed' need a target that
-- actually has dual objects) gives 'retract' below plenty to sample from.
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
    [ propCategory @FREEKIND
    , propTerminalObject @FREEKIND
    , propInitialObject @FREEKIND
    , propBinaryProducts @FREEKIND (\ @a @b r -> withObProd @FINREL @(LowerT a) @(LowerT b) r)
    , propBinaryCoproducts @FREEKIND (\ @a @b r -> withObCoprod @FINREL @(LowerT a) @(LowerT b) r)
    , propClosed @FREEKIND
        (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
        (\ @a @b r -> withObExp @FINREL @(LowerT a) @(LowerT b) r)
    , propSymMonoidal @FREEKIND (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
    , -- 'propStarAutonomous' isn't wired in here: its naturality checks need e.g. an arbitrary
      -- @a ** b ~> Dual c@ for independently-drawn a,b,c, but in a *free* category that hom-set is
      -- genuinely empty for most palette triples (no unitor/associator-driven bridge connects a
      -- plain tensor shape to an unrelated dualized one) — 'genTerm' can't conjure a morphism that
      -- doesn't exist, so every sample gets discarded. 'propCompactClosed' avoids this: none of its
      -- checks need to *generate* a random Dual-involving morphism, only compose the fixed ones
      -- 'CompactClosed' already provides.
      propCompactClosed @FREEKIND
        (\ @a @b r -> withOb2 @FINREL @(LowerT a) @(LowerT b) r)
        (\r -> r)
    ]

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

-- | Decides whether two object shapes are the same, structurally — 'genTerm' uses this to
-- check whether a generator branch's source\/target actually lines up with the shape it wants
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

-- | The finite palette of shapes 'Testable' picks 'Some' objects from — reused here (via
-- 'theFree', recovered from each 'Some' value's bundled 'KnownFree') so 'genTerm' can try
-- composing through each of them (see 'genTerm'\'s @composeB@, and the note on why it avoids
-- 'Testable.genSome' there).
type Palette = '[InitF, TermF, TermF *! TermF, TermF + TermF, UnitF, TermF **! TermF]

palette :: [Some FREEKIND]
palette = mkSomeList @FREEKIND @Palette

-- | Generate a random term between two (given) object shapes. Most branches recurse
-- structurally on a strictly smaller sub-shape of the source or target, so they always
-- terminate on their own; @composeB@ is the exception (it can reach into an unrelated object
-- via composition), so it's the one branch bounded by @fuel@, which decreases on every
-- recursive call and cuts it off at zero.
genTerm :: forall a b. (Ob a, Ob b) => Int -> SFree a -> SFree b -> GenTotal (Free a b)
genTerm fuel sa sb =
  oneOfTotal [idB, initiateB, terminateB, fstSndB, applyB, recB]
  where
    recB
      | fuel <= 0 = empty
      | otherwise = oneOfTotal [prodB, sumSrcB, sumTgtB, curryB, composeB]
    idB = case eqSFree sa sb of
      Just Refl -> pure id
      Nothing -> empty
    initiateB = case sa of
      SInit -> pure initiate
      _ -> empty
    terminateB = case sb of
      STerm -> pure terminate
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
    -- Route through every palette shape as a possible intermediate object. This is what lets
    -- the generator ever compose two otherwise-unrelated terms together.
    composeB =
      oneOfTotal
        [ (.) <$> genTerm (fuel - 1) (theFree @mid) sb <*> genTerm (fuel - 1) sa (theFree @mid)
        | Some @mid <- palette
        ]

-- | Bridges straight to 'FINREL'\'s 'Ob' rather than its 'TestOb' — 'Testable FINREL' leaves
-- 'TestOb' at its class default ('type TestOb a = Ob a'), and an unrestated default associated
-- type equation doesn't get unfolded through an abstract type variable the way an explicit
-- instance override (like 'CategoryOf FINREL'\'s own 'Ob' equation) does.
instance Testable FREEKIND where
  type TestOb a = (KnownFree a, Ob (LowerT a))
  showOb @a = showSFree (theFree @a)
  eqOb @a @b = eqSFree (theFree @a) (theFree @b)
  genSome = genSomeDef @Palette

-- | Two terms are equal iff they denote the same relation once interpreted into 'FINREL' via
-- 'retract' — decided by 'FinRel'\'s own 'Eq'. Structural equality on 'Free' terms would be too
-- strict for testing categorical laws: e.g. @'terminate' . f@ and @'terminate'@ are built from
-- different 'Free' constructors even though uniqueness of the terminal object makes them denote
-- the same morphism.
instance (TestOb a, TestOb b) => TestingEqShow (Free (a :: FREEKIND) b) where
  eqP l r = pure (retract @FREECS @(Rep Interp) l == retract @FREECS @(Rep Interp) r)

instance (TestOb a, TestOb b) => TestableType (Free (a :: FREEKIND) b) where
  gen = genTerm 3 (theFree @a) (theFree @b)
instance TestableProfunctor (Free :: CAT FREEKIND)
