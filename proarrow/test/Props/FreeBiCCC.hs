{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.FreeBiCCC where

import Control.Applicative (Alternative (..))
import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:) (..))
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (fst, id, snd, (.))

import Proarrow.Category.Instance.FreeBiCCC (FBC (..), KnownFBCOb (fbcCase), Lower, Term (..), interp)
import Proarrow.Core (CAT, CategoryOf (..))

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
  , eqHask
  , genSomeDef
  , oneOfTotal
  )

-- | The free BiCCC's only generator: a single primitive morphism, just enough to make the
-- terms non-trivial.
data Prim a b where
  NotP :: Prim Bool Bool

interpPrim :: Prim a b -> a -> b
interpPrim NotP = not

test :: TestTree
test =
  testGroup
    "FreeBiCCC"
    [ propCategory @(FBC Prim)
    , propTerminalObject @(FBC Prim)
    , propInitialObject @(FBC Prim)
    , propBinaryProducts @(FBC Prim) (\r -> r)
    , propBinaryCoproducts @(FBC Prim) (\r -> r)
    , propClosed @(FBC Prim) (\r -> r) (\r -> r)
    ]

-- | A shallow singleton witnessing only the /top-level/ shape of an object expression — one
-- level of case analysis, exactly like 'fbcCase' itself, rather than a deep tree mirroring the
-- whole 'FBC' structure. Recovering a sub-object's own shape (to recurse) is just another call
-- to 'theFBC', not a stored field, since 'Ob'\/'FBCTestOb' of the sub-object (bundled on the
-- constructor) is already enough to make that call.
data SFBC (a :: FBC Prim) where
  SObj :: (TestOb (x :: Type)) => SFBC (OBJ x)
  SUnit :: SFBC UNIT
  SProd :: (Ob a, Ob b, FBCTestOb a, FBCTestOb b) => SFBC (PROD a b)
  SZero :: SFBC ZERO
  SSum :: (Ob a, Ob b, FBCTestOb a, FBCTestOb b) => SFBC (SUM a b)
  SExpo :: (Ob a, Ob b, FBCTestOb a, FBCTestOb b) => SFBC (EXPO a b)

-- | Threads 'TestOb' down to every embedded base object in an 'FBC' shape — the one thing
-- 'KnownFBCOb'\'s library-level case analysis can't provide on its own, since it only ever
-- knows about 'Ob', not this test suite's (richer) notion of "generatable".
type family FBCTestOb (a :: FBC Prim) :: Constraint where
  FBCTestOb (OBJ x) = TestOb (x :: Type)
  FBCTestOb UNIT = ()
  FBCTestOb (PROD a b) = (FBCTestOb a, FBCTestOb b)
  FBCTestOb ZERO = ()
  FBCTestOb (SUM a b) = (FBCTestOb a, FBCTestOb b)
  FBCTestOb (EXPO a b) = (FBCTestOb a, FBCTestOb b)

-- | Recover the shape singleton by case analysis via 'fbcCase' — no per-shape instances needed,
-- unlike the 'KnownFBCOb' this leans on: 'FBCTestOb' supplies the one extra thing 'fbcCase'
-- doesn't know about (leaf-level 'TestOb'), and 'fbcCase' supplies the rest. Since 'SFBC' is
-- shallow, each constructor's own bundled evidence is exactly what 'fbcCase' hands it — no
-- recursive construction needed here at all.
theFBC :: forall a. (KnownFBCOb a, FBCTestOb a) => SFBC a
theFBC = fbcCase @a SObj SUnit SProd SZero SSum SExpo

-- | Decides whether two object shapes are the same, structurally — 'genTerm' uses this to
-- check whether a generator branch's source\/target actually lines up with the shape it wants
-- to produce. The only case that needs real work is 'SObj': deciding whether two embedded base
-- objects are equal isn't decidable from shape alone, so it defers to 'eqOb' (i.e. to whatever
-- 'Testable' says an object of the base category is, e.g. 'Data.Typeable.eqT' for 'Type').
-- Sub-shapes aren't stored (see 'SFBC'), so comparing them recurses through a fresh 'theFBC'.
eqSFBC :: SFBC a -> SFBC b -> Maybe (a :~: b)
eqSFBC (SObj @x) (SObj @y) = (\Refl -> Refl) <$> eqOb @Type @x @y
eqSFBC SUnit SUnit = Just Refl
eqSFBC (SProd @a1 @a2) (SProd @b1 @b2) = case (eqSFBC (theFBC @a1) (theFBC @b1), eqSFBC (theFBC @a2) (theFBC @b2)) of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
eqSFBC SZero SZero = Just Refl
eqSFBC (SSum @a1 @a2) (SSum @b1 @b2) = case (eqSFBC (theFBC @a1) (theFBC @b1), eqSFBC (theFBC @a2) (theFBC @b2)) of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
eqSFBC (SExpo @a1 @a2) (SExpo @b1 @b2) = case (eqSFBC (theFBC @a1) (theFBC @b1), eqSFBC (theFBC @a2) (theFBC @b2)) of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
eqSFBC _ _ = Nothing

-- | The finite palette of shapes 'Testable' picks 'Some' objects from — reused here (via
-- 'theFBC', recovered from each 'Some' value's bundled 'TestOb') so 'genTerm' can try
-- composing through each of them (see 'genTerm'\'s @composeB@, and the note on why it avoids
-- 'Testable.genSome' there).
type Palette =
  '[OBJ Bool, UNIT, PROD (OBJ Bool) (OBJ Bool), SUM (OBJ Bool) (OBJ Bool), EXPO (OBJ Bool) (OBJ Bool), ZERO]

palette :: [Some (FBC Prim)]
palette = mkSomeList @(FBC Prim) @Palette

-- | Render an object shape for test failure output.
showSFBC :: SFBC a -> String
showSFBC (SObj @x) = showOb @Type @x
showSFBC SUnit = "UNIT"
showSFBC (SProd @a @b) = "(" ++ showSFBC (theFBC @a) ++ " && " ++ showSFBC (theFBC @b) ++ ")"
showSFBC SZero = "ZERO"
showSFBC (SSum @a @b) = "(" ++ showSFBC (theFBC @a) ++ " || " ++ showSFBC (theFBC @b) ++ ")"
showSFBC (SExpo @a @b) = "(" ++ showSFBC (theFBC @a) ++ " ~~> " ++ showSFBC (theFBC @b) ++ ")"

-- | Generate a random term between two (given) object shapes. Most branches recurse
-- structurally on a strictly smaller sub-shape of the source or target, so they always
-- terminate on their own; @composeB@ is the exception (it can reach into an unrelated object
-- via composition, e.g. to route through an 'Apply' or an embedded generator that the
-- structural branches alone can't reach), so it's the one branch bounded by @fuel@, which
-- decreases on every recursive call and cuts it off at zero.
genTerm :: forall a b. (Ob a, FBCTestOb a, Ob b, FBCTestOb b) => Int -> GenTotal (Term a b)
genTerm fuel =
  oneOfTotal [idB, terminateB, absurdB, fstSndB, applyB, embB, recB]
  where
    sa = theFBC @a
    sb = theFBC @b
    recB
      | fuel <= 0 = empty
      | otherwise = oneOfTotal [prodB, sumSrcB, sumTgtB, expoB, composeB]
    idB = case eqSFBC sa sb of
      Just Refl -> pure Id
      Nothing -> empty
    terminateB = case sb of
      SUnit -> pure Terminate
      _ -> empty
    absurdB = case sa of
      SZero -> pure Absurd
      _ -> empty
    prodB = case sb of
      SProd @b1 @b2 -> Pair <$> genTerm @a @b1 (fuel - 1) <*> genTerm @a @b2 (fuel - 1)
      _ -> empty
    sumSrcB = case sa of
      SSum @a1 @a2 -> Case <$> genTerm @a1 @b (fuel - 1) <*> genTerm @a2 @b (fuel - 1)
      _ -> empty
    sumTgtB = case sb of
      SSum @b1 @b2 -> oneOfTotal [Compose Inl <$> genTerm @a @b1 (fuel - 1), Compose Inr <$> genTerm @a @b2 (fuel - 1)]
      _ -> empty
    expoB = case sb of
      SExpo @b1 @b2 -> Curry <$> genTerm @(PROD a b1) @b2 (fuel - 1)
      _ -> empty
    -- Route through every palette shape as a possible intermediate object. This is what lets
    -- the generator ever produce e.g. an 'Apply', or compose two embedded generators.
    composeB =
      oneOfTotal
        [ Compose <$> genTerm @mid @b (fuel - 1) <*> genTerm @a @mid (fuel - 1)
        | Some @mid <- palette
        ]
    -- a ~ PROD (EXPO ea1 ea2) r, with r ~ ea1 and b ~ ea2.
    applyB = case sa of
      SProd @sl @sr -> case theFBC @sl of
        SExpo @sea1 @sea2 -> case (eqSFBC (theFBC @sr) (theFBC @sea1), eqSFBC sb (theFBC @sea2)) of
          (Just Refl, Just Refl) -> pure Apply
          _ -> empty
        _ -> empty
      _ -> empty
    fstSndB = case sa of
      SProd @sa1 @sa2 ->
        oneOfTotal
          [ case eqSFBC sb (theFBC @sa1) of Just Refl -> pure Fst; Nothing -> empty
          , case eqSFBC sb (theFBC @sa2) of Just Refl -> pure Snd; Nothing -> empty
          ]
      _ -> empty
    embB = case (sa, sb) of
      (SObj @x, SObj @y) -> case (eqOb @Type @x @Bool, eqOb @Type @y @Bool) of
        (Just Refl, Just Refl) -> pure (Emb NotP)
        _ -> empty
      _ -> empty

instance Testable (FBC Prim) where
  type TestOb a = (KnownFBCOb a, FBCTestOb a, TestOb (Lower a))
  showOb @a = showSFBC (theFBC @a)
  eqOb @a @b = eqSFBC (theFBC @a) (theFBC @b)
  genSome = genSomeDef @Palette

-- | Render a 'Term' as the operator expression it's built from, e.g. @"curry (fst . not)"@.
showTerm :: Term (a :: FBC Prim) b -> String
showTerm Id = "id"
showTerm (Compose g f) = showTerm g ++ " . " ++ showTerm f
showTerm (Emb NotP) = "not"
showTerm Terminate = "terminate"
showTerm Absurd = "absurd"
showTerm Fst = "fst"
showTerm Snd = "snd"
showTerm (Pair f g) = "(" ++ showTerm f ++ " &&& " ++ showTerm g ++ ")"
showTerm Inl = "inl"
showTerm Inr = "inr"
showTerm (Case f g) = "(" ++ showTerm f ++ " ||| " ++ showTerm g ++ ")"
showTerm (Curry f) = "curry (" ++ showTerm f ++ ")"
showTerm Apply = "apply"

-- | Two terms are equal iff they denote the same function once interpreted into 'Type' —
-- decided semantically (by sampling, via 'eqHask'), not by a symbolic decision procedure.
instance (TestOb a, TestOb b) => TestingEqShow (Term (a :: FBC Prim) b) where
  eqP l r = eqHask (interp interpPrim l) (interp interpPrim r)
  showP = showTerm

instance (TestOb a, TestOb b) => TestableType (Term (a :: FBC Prim) b) where
  gen = genTerm @a @b 3
instance TestableProfunctor (Term :: CAT (FBC Prim))
