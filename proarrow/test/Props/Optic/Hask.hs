-- | Checks that optic subtyping works: any optic can be used directly where a weaker flavor is
-- needed (iso -> lens/prism -> affine traversal -> traversal -> setter, and the fold side),
-- because the consumers only ask for a @'SubFlavor' w need@ constraint, like the @Is k l@ class
-- of the @optics@ library.
--
-- The conversion functions below are compile-time tests: each one only typechecks if the
-- corresponding 'SubFlavor' instance exists. The 'TestTree' then checks at runtime that a lens,
-- prism or iso handed directly to the getter\/setter\/fold\/review\/preview consumers still acts
-- like the optic it came from.
module Props.Optic.Hask where

import Control.Monad (unless)
import Data.Bifunctor (bimap, first, second)
import Data.Maybe (maybeToList)
import Data.Tuple (swap)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (Property, genWith, testFailed, testProperty)
import Prelude

import GHC.Generics qualified as G
import Proarrow.Category.Monoidal (Monoidal)
import Proarrow.Category.Monoidal.Action (ProdAction)
import Proarrow.Category.Monoidal.Distributive (Bicartesian, StrongDistributiveProfunctor, baseTraverse)
import Proarrow.Category.Monoidal.Strength (Strong)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts, type (||))
import Proarrow.Core (CategoryOf (..), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, type (&&))
import Proarrow.Optic qualified as O
import Proarrow.Optic.AffineFold (AffineFold, preview, (^?))
import Proarrow.Optic.AffineTraversal (AffineTraversal)
import Proarrow.Optic.Fold (Fold, foldMapOf, unfold)
import Proarrow.Optic.Getter (Getter, Review, review, view, (#), (^.))
import Proarrow.Optic.Grate (Grate, grate, withGrate)
import Proarrow.Optic.Iso (Iso, fromPIso, toPIso, withIso)
import Proarrow.Optic.Kaleidoscope (Kaleidoscope, Nat (..), kaleidoscope, kaleidoscopeN, kaleidoscopeOf)
import Proarrow.Optic.Lens (Lens, lens, withLens)
import Proarrow.Optic.MonoidalLens (MonoidalLens, monLens)
import Proarrow.Optic.Prism (Prism, fromOpLens, prism, toOpLens, withPrism)
import Proarrow.Optic.Setter (Setter, SetterRes (..), over, set, (%~))
import Proarrow.Optic.Tracer (Tracer, fromPTracer, toPTracer, tracer, tracerOf, withTracer)

import Proarrow.Optic.MonoidalTraversal
  ( MonoidalTraversal
  , PTraversal
  , fromPTraversal
  , monTraverseOf
  , multOptic
  , par1Optic
  , plusOptic
  , toPTraversal
  , u1Optic
  )
import Proarrow.Optic.Traversal (TravRes, Traversal, traverseOf)

import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Functor (Prelude (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (CorepStar (..), RepCostar (..), Representable)
import Proarrow.Promonad.Reader (Reader (..))
import Proarrow.Promonad.Writer (Writer)

import Proarrow.Testing (GenTotal (..), TestableType (..), pattern GenNonEmpty)
import Props.Hask ()

-- * The subtyping lattice

isoToLens :: (CategoryOf k) => Iso (s :: k) t a b -> Lens s t a b
isoToLens = O.convert

-- | Compile-time proof of the theorem "every representable residual is a Setter": 'overP' for
-- the @(t, RepCostar t)@ witness resolves from just 'Representable' t -- no 'Traversable'. If the
-- old @Traversable t@ constraint were re-added to that instance, this would stop compiling.
representableResidualIsSetter
  :: forall {k} (t :: k +-> k) s a b t'
   . (Representable t, Bicartesian k) => t s a -> RepCostar t b t' -> (a ~> b) -> (s ~> t')
representableResidualIsSetter = overP

-- | Dually: every corepresentable residual is a Setter, from just 'Corepresentable' t.
corepresentableResidualIsSetter
  :: forall {k} (t :: k +-> k) s a b t'
   . (Corepresentable t, Bicartesian k) => CorepStar t s a -> t b t' -> (a ~> b) -> (s ~> t')
corepresentableResidualIsSetter = overP

isoToPrism :: (CategoryOf k) => Iso (s :: k) t a b -> Prism s t a b
isoToPrism = O.convert

isoToGetter :: (CategoryOf k) => Iso (s :: k) t a b -> Getter s t a b
isoToGetter = O.convert

isoToReview :: (CategoryOf k) => Iso (s :: k) t a b -> Review s t a b
isoToReview = O.convert

isoToGrate :: (CategoryOf k) => Iso (s :: k) t a b -> Grate s t a b
isoToGrate = O.convert

isoToKaleidoscope :: (Monoidal k) => Iso (s :: k) t a b -> Kaleidoscope s t a b
isoToKaleidoscope = O.convert

-- | The classic zipping grate on pairs.
pairGrate :: Grate (Bool, Bool) (Bool, Bool) Bool Bool
pairGrate = grate (\k -> (k fst, k snd))

lensToAffineTraversal :: (CategoryOf k) => Lens (s :: k) t a b -> AffineTraversal s t a b
lensToAffineTraversal = O.convert

lensToGetter :: (CategoryOf k) => Lens (s :: k) t a b -> Getter s t a b
lensToGetter = O.convert

lensToTraversal :: (CategoryOf k) => Lens (s :: k) t a b -> Traversal s t a b
lensToTraversal = O.convert

lensToSetter :: (CategoryOf k) => Lens (s :: k) t a b -> Setter s t a b
lensToSetter = O.convert

lensToAffineFold :: (CategoryOf k) => Lens (s :: k) t a b -> AffineFold s t a b
lensToAffineFold = O.convert

lensToFold :: (CategoryOf k) => Lens (s :: k) t a b -> Fold s t a b
lensToFold = O.convert

prismToAffineTraversal :: (CategoryOf k) => Prism (s :: k) t a b -> AffineTraversal s t a b
prismToAffineTraversal = O.convert

prismToReview :: (CategoryOf k) => Prism (s :: k) t a b -> Review s t a b
prismToReview = O.convert

prismToTraversal :: (CategoryOf k) => Prism (s :: k) t a b -> Traversal s t a b
prismToTraversal = O.convert

prismToSetter :: (CategoryOf k) => Prism (s :: k) t a b -> Setter s t a b
prismToSetter = O.convert

prismToAffineFold :: (CategoryOf k) => Prism (s :: k) t a b -> AffineFold s t a b
prismToAffineFold = O.convert

prismToFold :: (CategoryOf k) => Prism (s :: k) t a b -> Fold s t a b
prismToFold = O.convert

affineTraversalToTraversal :: (CategoryOf k) => AffineTraversal (s :: k) t a b -> Traversal s t a b
affineTraversalToTraversal = O.convert

affineTraversalToSetter :: (CategoryOf k) => AffineTraversal (s :: k) t a b -> Setter s t a b
affineTraversalToSetter = O.convert

affineTraversalToAffineFold :: (CategoryOf k) => AffineTraversal (s :: k) t a b -> AffineFold s t a b
affineTraversalToAffineFold = O.convert

affineTraversalToFold :: (CategoryOf k) => AffineTraversal (s :: k) t a b -> Fold s t a b
affineTraversalToFold = O.convert

getterToAffineFold :: (CategoryOf j, CategoryOf k) => Getter (s :: k) (t :: j) a b -> AffineFold s t a b
getterToAffineFold = O.convert

getterToFold :: (CategoryOf j, CategoryOf k) => Getter (s :: k) (t :: j) a b -> Fold s t a b
getterToFold = O.convert

traversalToSetter :: (CategoryOf k) => Traversal (s :: k) t a b -> Setter s t a b
traversalToSetter = O.convert

traversalToFold :: (CategoryOf k) => Traversal (s :: k) t a b -> Fold s t a b
traversalToFold = O.convert

-- | Compile-time proof that 'traverseOf' distributes an /arbitrary/ 'StrongDistributiveProfunctor'
-- (Traversable-style), not just a @'Star' f@: this only typechecks because the carrier @p@ is
-- fully polymorphic.
traverseOfIsGeneric
  :: (StrongDistributiveProfunctor p, Strong ProdAction p) => p Bool Bool -> p (Bool, Bool) (Bool, Bool)
traverseOfIsGeneric = traverseOf _1

affineFoldToFold :: (CategoryOf j, CategoryOf k) => AffineFold (s :: k) (t :: j) a b -> Fold s t a b
affineFoldToFold = O.convert

-- | Composites convert to the meet of their flavors, in one step.
compositeToAffineTraversal
  :: (CategoryOf k) => Lens (s :: k) t a b -> Prism a b c d -> AffineTraversal s t c d
compositeToAffineTraversal l p = O.convert (l O.% p)

grateToSetter :: (CategoryOf k) => Grate (s :: k) t a b -> Setter s t a b
grateToSetter = O.convert

tracerToSetter :: (CategoryOf k) => Tracer (s :: k) t a b -> Setter s t a b
tracerToSetter = O.convert

isoToTracer :: (CategoryOf k) => Iso (s :: k) t a b -> Tracer s t a b
isoToTracer = O.convert

-- | A tracer converts to a flipped setter (its witnesses are a setter's, read backwards); the
-- converse has no instance, since a flipped setter need not have a trace.
tracerToFlipSetter :: (CategoryOf k) => Tracer (s :: k) t a b -> O.Optic (O.Prostrong (O.Flip SetterRes)) s t a b
tracerToFlipSetter = O.convert

-- * The reversed (Flip) side of the lattice, reached via 're'

reLensIsReview :: (CategoryOf k, Ob (a :: k), Ob b) => Lens s t a b -> Review b a t s
reLensIsReview = O.convert . O.re

rePrismIsGetter :: (CategoryOf k, Ob (a :: k), Ob b) => Prism s t a b -> Getter b a t s
rePrismIsGetter = O.convert . O.re

reIsoIsGetter :: (CategoryOf k, Ob (a :: k), Ob b) => Iso s t a b -> Getter b a t s
reIsoIsGetter = O.convert . O.re

reReLens :: (CategoryOf k, Ob (s :: k), Ob t, Ob a, Ob b) => Lens s t a b -> Lens s t a b
reReLens = O.convert . O.re . O.re

-- * Honest constraints

-- | Compile-time check: building and eliminating a lens needs only binary products, never
-- 'Proarrow.Category.Monoidal.Distributive.Bicartesian', even though 'AffineTravRes' sits above
-- 'Proarrow.Optic.Lens.LensRes' in the flavor hierarchy.
lensLegs :: (HasBinaryProducts k) => Lens (s :: k) t a b -> (s ~> a, (s && b) ~> t)
lensLegs l = withLens l (,)

-- | Compile-time check: building and eliminating a prism needs only binary coproducts.
prismLegs :: (HasBinaryCoproducts k) => Prism (s :: k) t a b -> (b ~> t, s ~> (t || a))
prismLegs p = withPrism p (,)

-- * Runtime checks in Hask, using the optics directly where a weaker flavor is needed

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\((_, c), b) -> (b, c))

_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just (maybe (Left Nothing) Right)

-- | A monoidal lens onto the second component (@Type@'s tensor is @(,)@, so it coincides with a
-- product lens here).
_2mon :: MonoidalLens (Bool, Bool) (Bool, Bool) Bool Bool
_2mon = monLens @Bool id id

notIso :: Iso Bool Bool Bool Bool
notIso = O.iso not not

-- | The binary (pair) kaleidoscope, focusing both components of a tensor.
pairK :: Kaleidoscope (Bool, Bool) (Bool, Bool) Bool Bool
pairK = kaleidoscope id id

-- | The arity-3 kaleidoscope (via the general 'kaleidoscopeN'), over a nested tensor triple.
triK :: Kaleidoscope (Bool, (Bool, (Bool, ()))) (Bool, (Bool, (Bool, ()))) Bool Bool
triK = kaleidoscopeN @(S (S (S Z))) id id

-- | A tracer in Hask with a @Bool@ residual and identity legs, so @over feedback f s@ solves
-- @(m, t) = f (m, s)@ for @m@ through the lazy fixpoint of @'Proarrow.Category.Monoidal.Strength.Costrong' (->)@.
feedback :: Tracer Bool Bool (Bool, Bool) (Bool, Bool)
feedback = tracer @Bool id id

-- | Focus function for 'feedback': the new residual is @not s@ and the new target is the residual,
-- so the loop computes @not@.
loop :: (Bool, Bool) -> (Bool, Bool)
loop (m, s) = (not s, m)

-- | The same encoding-agnostic 'O.iso' at the profunctor-class-flavored traversal type.
tIsoNot :: PTraversal Bool Bool Bool Bool
tIsoNot = O.iso not not

-- | The same iso in the profunctor-class-flavored encoding, to check that the consumers are
-- encoding-agnostic.
cNot :: O.PIso Bool Bool Bool Bool
cNot = O.iso not not

cMaybeNot :: O.PIso (Maybe Bool) (Maybe Bool) (Maybe Bool) (Maybe Bool)
cMaybeNot = O.iso (fmap not) (fmap not)

swapIso :: Iso (Bool, Bool) (Bool, Bool) (Bool, Bool) (Bool, Bool)
swapIso = O.iso swap swap

notMaybeIso :: Iso (Maybe Bool) (Maybe Bool) (Maybe Bool) (Maybe Bool)
notMaybeIso = O.iso (fmap not) (fmap not)

-- | Run 'traverseOf' on a profunctor-class-flavored 'PTraversal'.
travPar1 :: Bool -> Maybe Bool
travPar1 b = G.unPar1 <$> unPrelude (unStar (traverseOf (fromPTraversal par1Optic) (Star (Prelude . Just . not))) (G.Par1 b))

-- | Check two Hask arrows for semantic equality on generated inputs.
propFnEq :: forall a b. (TestableType a, Show a, Show b, Eq b) => String -> (a -> b) -> (a -> b) -> TestTree
propFnEq nm f g = testProperty nm case gen @a of
  GenEmpty _ -> pure ()
  GenNonEmpty ga -> do
    a <- genWith (Just . show) ga
    assertEq (f a) (g a)

assertEq :: (Show b, Eq b) => b -> b -> Property ()
assertEq l r = unless (l == r) (testFailed (show l ++ " /= " ++ show r))

test :: TestTree
test =
  testGroup
    "Optic subtyping"
    [ propFnEq @(Bool, Bool) "lens as getter" (view _1) fst
    , propFnEq @(Bool, Bool) "lens as getter (^.)" (^. _1) fst
    , propFnEq @(Bool, Bool) "lens as setter" (over _1 not) (first not)
    , propFnEq @(Bool, Bool) "set lens" (set _1 False) (\(_, c) -> (False, c))
    , propFnEq @(Bool, Bool) "lens as affine fold" (preview _1) (Left . fst)
    , propFnEq @(Bool, Bool) "lens as fold" (foldMapOf _1 (: [])) (\(a, _) -> [a])
    , propFnEq @(Bool, Bool) "monoidal lens as setter" (over _2mon not) (second not)
    , propFnEq @(Bool, Bool) "monoidal lens as getter" (view _2mon) snd
    , propFnEq @(Bool, Bool)
        "traverseOf lens"
        (unPrelude . unStar (traverseOf _1 (Star (Prelude . Just . not))))
        (Just . first not)
    , propFnEq @Bool "prism as review" (review _Just) Just
    , propFnEq @Bool "prism as review (#)" (_Just #) Just
    , propFnEq @(Maybe Bool) "prism as setter" (_Just %~ not) (fmap not)
    , propFnEq @(Maybe Bool) "prism as affine fold" (preview _Just) (maybe (Right ()) Left)
    , propFnEq @(Maybe Bool) "prism as fold" (foldMapOf _Just (: [])) maybeToList
    , propFnEq @(Maybe Bool) "prism as preview" (^? _Just) id
    , propFnEq @Bool "prism ~ op-lens: fromOpLens . toOpLens preserves review" (review (fromOpLens (toOpLens _Just))) Just
    , propFnEq @Bool "prism unfold: build a Maybe through the review leg" (unfold (toOpLens _Just) not) (\x -> Just (not x))
    , propFnEq @(Maybe Bool)
        "prism ~ op-lens: fromOpLens . toOpLens preserves setter"
        (fromOpLens (toOpLens _Just) %~ not)
        (fmap not)
    , propFnEq @Bool "iso as getter" (view notIso) not
    , propFnEq @Bool "iso as review" (review notIso) not
    , propFnEq @Bool "iso as setter" (over notIso not) not
    , propFnEq @Bool "iso as kaleidoscope" (kaleidoscopeOf notIso not) not
    , propFnEq @Bool "iso as monoidal lens (view)" (view (O.convert notIso :: MonoidalLens Bool Bool Bool Bool)) not
    , propFnEq @Bool "iso as monoidal lens (over)" (over (O.convert notIso :: MonoidalLens Bool Bool Bool Bool) not) not
    , propFnEq @(Bool, Bool) "lens as traversal as setter" (over (lensToTraversal _1) not) (first not)
    , propFnEq @(Maybe Bool) "prism as traversal as fold" (foldMapOf (prismToTraversal _Just) (: [])) maybeToList
    , propFnEq @(Bool, Bool) "kaleidoscope as setter (hom carrier)" (kaleidoscopeOf pairK not) (bimap not not)
    , propFnEq @(Bool, Bool)
        "kaleidoscope aggregates through an applicative"
        (\ss -> unPrelude (unStar (kaleidoscopeOf pairK (Star (Prelude . okIf))) ss))
        aggBoth
    , propFnEq @(Bool, Bool)
        "kaleidoscope as fold (it is a fixed-arity traversal)"
        (foldMapOf pairK (: []))
        (\(a, b) -> [a, b])
    , propFnEq @(Bool, Bool)
        "kaleidoscope as traversal"
        (unPrelude . unStar (traverseOf pairK (Star (Prelude . Just . not))))
        (\(a, b) -> Just (not a, not b))
    , propFnEq @(Bool, Bool) "corep-cotraversable witness as traversal (over)" (over zipSnd not) (second not)
    , propFnEq @(Bool, Bool)
        "corep-cotraversable witness as traversal (traverseOf)"
        (unPrelude . unStar (traverseOf zipSnd (Star (Prelude . Just . not))))
        (Just . second not)
    , propFnEq @(Bool, (Bool, (Bool, ()))) "n-ary (3) kaleidoscope as setter" (kaleidoscopeOf triK not) mapTriple
    , propFnEq @(Bool, (Bool, (Bool, ())))
        "n-ary (3) kaleidoscope aggregates through an applicative"
        (\ss -> unPrelude (unStar (kaleidoscopeOf triK (Star (Prelude . okIf))) ss))
        aggTriple
    , propFnEq @(Bool, Bool) "re lens as review" (review (O.re _1)) fst
    , propFnEq @Bool "re prism as getter" (view (O.re _Just)) Just
    , propFnEq @Bool "re iso as getter" (view (O.re notIso)) not
    , propFnEq @(Bool, Bool) "re re lens as getter" (view (reReLens _1)) fst
    , propFnEq @Bool "view on constraint-flavored iso" (view cNot) not
    , propFnEq @Bool "review on constraint-flavored iso" (review cNot) not
    , propFnEq @Bool "over on constraint-flavored iso" (over cNot not) not
    , propFnEq @Bool "traverseOf on PTraversal" travPar1 (Just . not)
    , propFnEq @Bool
        "iso constructed as PTraversal"
        (unPrelude . unStar (traverseOf (fromPTraversal tIsoNot) (Star (Prelude . Just . not))))
        (Just . not)
    , propFnEq @Bool "over on a PTraversal" (over tIsoNot not) not
    , propFnEq @(Bool, Bool) "grate as setter" (over pairGrate not) (bimap not not)
    , propFnEq @(Bool, Bool) "set on a grate" (set pairGrate True) (const (True, True))
    , propFnEq @Bool "iso as grate as setter" (over (isoToGrate notIso) not) not
    , propFnEq @Bool "tracer feeds the residual back through the focus" (over feedback loop) not
    , propFnEq @Bool "set on a tracer" (set feedback (True, False)) (const False)
    , propFnEq @(Bool, Bool) "re-over a tracer runs it backwards, no trace needed" (over (O.re feedback) not) (second not)
    , propFnEq @(Bool, Bool)
        "re-over a tracer converted to a flipped setter"
        (over (O.re (tracerToFlipSetter feedback)) not)
        (second not)
    , propFnEq @Bool "iso as tracer" (tracerOf notIso not) not
    , propFnEq @Bool "iso as tracer as setter" (over (isoToTracer notIso) not) not
    , propFnEq @Bool "PTracer round trip" (over (fromPTracer (toPTracer feedback)) loop) not
    , propFnEq @(Bool, Bool)
        "withTracer legs of a tracer compose to the identity"
        (\b -> withTracer feedback (\h i -> h (i b)))
        id
    , propFnEq @(Bool, Bool)
        "withTracer on an iso%tracer composite"
        (\b -> withTracer (notIso O.% feedback) (\h i -> h (i b)))
        id
    , propFnEq @(Bool, Bool) "withTracer on a PTracer" (\b -> withTracer (toPTracer feedback) (\h i -> h (i b))) id
    , propFnEq @(Bool, Bool) "composite lens%tracer over" (over (_1 O.% feedback) loop) (first not)
    , propFnEq @Bool "withIso on constraint-flavored iso" (withIso cNot const) not
    , propFnEq @Bool "withIso on re-versed iso" (withIso (O.re notIso) const) not
    , propFnEq @(Bool, Bool) "withLens on an iso" (withLens swapIso const) swap
    , propFnEq @(Bool, Bool) "withLens put leg on an iso" (withLens swapIso (\_ sbt -> curry sbt (True, False))) swap
    , propFnEq @(Maybe Bool)
        "withPrism on an iso"
        (withPrism (isoToPrism notMaybeIso) (\_ sta -> sta))
        (Right . fmap not)
    , propFnEq @Bool "withGrate zipping" (\b -> withGrate (isoToGrate notIso) (\z -> z (\g -> g ()) (\() -> b))) id
    , propFnEq @Bool "withLens on a PIso" (withLens cNot const) not
    , propFnEq @(Maybe Bool) "preview on a PIso" (^? cMaybeNot) (Just . fmap not)
    , propFnEq @Bool "PIso round trip" (view (fromPIso (toPIso notIso))) not
    , propFnEq @Bool "over via fromPIso" (over (fromPIso cNot) not) not
    , propFnEq @(Maybe Bool)
        "PTraversal round trip (prism is a MonoidalTraversal)"
        (over (fromPTraversal (toPTraversal (O.convert _Just :: MonoidalTraversal (Maybe Bool) (Maybe Bool) Bool Bool))) not)
        (fmap not)
    , -- Step 4: monTraverseOf distributes an SDP carrier through a prism (a MonoidalTraversal) with
      -- NO product-strength constraint on the carrier -- that's the point of the MonTravRes split.
      propFnEq @(Maybe Bool)
        "monTraverseOf a prism (MonoidalTraversal) with a list effect"
        (\m -> unPrelude (unStar (monTraverseOf _Just (Star (Prelude . ((\b -> [b, not b]) :: Bool -> [Bool])))) m))
        (traverse (\b -> [b, not b]))
    , propFnEq @(Bool, Bool)
        "fromPTraversal over both"
        (\(x, y) -> unPar2 (over fromBoth not (par2 x y)))
        (bimap not not)
    , propFnEq @(Bool, Bool)
        "fromPTraversal foci order"
        (\(x, y) -> foldMapOf fromBoth (: []) (par2 x y))
        (\(x, y) -> [x, y])
    , propFnEq @Bool "fromPTraversal on a sum, left" (\x -> foldMapOf fromEither (: []) (G.L1 (G.Par1 x))) (: [])
    , propFnEq @Bool
        "fromPTraversal on a sum, right"
        (\x -> unSum (over fromEither not (G.R1 (G.Par1 x))))
        (Right . not)
    , propFnEq @Bool
        "fromPTraversal with zero foci"
        (\_ -> foldMapOf (fromPTraversal (u1Optic @Bool)) (: []) G.U1)
        (const [])
    , propFnEq @(Maybe Bool, Bool)
        "composite lens%prism preview"
        (preview (_1 O.% _Just))
        (\(m, _) -> maybe (Right ()) Left m)
    , propFnEq @(Maybe Bool, Bool) "composite lens%prism over" (over (_1 O.% _Just) not) (first (fmap not))
    , propFnEq @(Maybe Bool, Bool)
        "traverseOf a lens%prism composite, no convert needed"
        (unPrelude . unStar (traverseOf (_1 O.% _Just) (Star (Prelude . (\b -> [b, not b])))))
        (\(m, c) -> [(m', c) | m' <- traverse (\b -> [b, not b]) m])
    , propFnEq @Bool "tracerOf a PTracer directly" (tracerOf (toPTracer feedback) loop) not
    , propFnEq @(Bool, Bool)
        "kaleidoscopeOf a kaleidoscope%iso composite"
        (kaleidoscopeOf (pairK O.% notIso) not)
        (bimap not not)
    , propFnEq @(Maybe Bool, Bool) "composite lens%prism fold" (foldMapOf (_1 O.% _Just) (: [])) (maybeToList . fst)
    , propFnEq @Bool "composite iso%prism review" (review (notMaybeIso O.% _Just)) (Just . not)
    , propFnEq @Bool "withPrism on composite" (withPrism (notMaybeIso O.% _Just) const) (Just . not)
    , propFnEq @(Maybe Bool, Bool)
        "converted composite preview"
        (preview (compositeToAffineTraversal _1 _Just))
        (\(m, _) -> maybe (Right ()) Left m)
    , propFnEq @(Maybe Bool, Bool)
        "cross-encoding composite over"
        (over (_1 O.% cMaybeNot) (fmap not))
        (first (fmap not))
    , -- exercise Writer's category-generic Traversable instance: distribute a real list effect
      -- through the writer functor (@Writer w % a = w ** a@, tensor-strength, any monoidal category).
      testProperty "Writer Traversable distributes a list effect" $
        assertEq
          (unPrelude (baseTraverse @(Writer [Bool]) @(Star (Prelude [])) (Prelude . \b -> [b, not b]) ([True], False)))
          [([True], False), ([True], True)]
    ]
  where
    bothPar = multOptic par1Optic par1Optic
    eitherPar = plusOptic par1Optic par1Optic
    fromBoth = fromPTraversal bothPar
    fromEither = fromPTraversal eitherPar
    par2 x y = G.Par1 x G.:*: G.Par1 y
    unPar2 (G.Par1 x G.:*: G.Par1 y) = (x, y)
    unSum (G.L1 (G.Par1 x)) = Left x
    unSum (G.R1 (G.Par1 y)) = Right y
    -- The former cotraversal, now a plain 'Traversal' via the kept
    -- @TravRes (CorepStar t) t@ instance (@t = Reader (OP Bool)@, a corepresentable
    -- 'Proarrow.Category.Monoidal.Distributive.Cotraversable' functor).
    zipSnd :: Traversal (Bool, Bool) (Bool, Bool) Bool Bool
    zipSnd =
      O.legs2prof @TravRes
        (CorepStar id :: CorepStar (Reader (OP Bool)) (Bool, Bool) Bool)
        (Reader id :: Reader (OP Bool) Bool (Bool, Bool))
    okIf b = if b then Just (not b) else Nothing
    aggBoth (x, y) = case (okIf x, okIf y) of (Just x', Just y') -> Just (x', y'); _ -> Nothing
    mapTriple (x, (y, (z, ()))) = (not x, (not y, (not z, ())))
    aggTriple (x, (y, (z, ()))) = case (okIf x, okIf y, okIf z) of (Just x', Just y', Just z') -> Just (x', (y', (z', ()))); _ -> Nothing
