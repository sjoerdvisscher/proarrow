{-# LANGUAGE AllowAmbiguousTypes #-}

{- HLINT ignore "Redundant id" -}

-- | Reusable law-checking properties, parameterized over any 'Testable' kind: 'testCategory',
-- 'testMonoidal', 'testBinaryProducts', 'testClosed', and friends. Wiring a new category into a
-- test suite is a 'Testable' instance plus calls to these; the @test/Props@ directory of
-- proarrow's source repository has many examples.
--
-- A @test@ returns a 'TestTree', ready for a 'Test.Tasty.testGroup'. A @prop@ returns a
-- @'Property' ()@, to be composed into a property of your own. Where both exist (e.g. 'testMonoid'
-- and 'propMonoid'), the @test@ one wraps the @prop@ one.
--
-- Many of these take an explicit witness that 'TestOb' is closed under the structure being tested
-- (e.g. that @'TestOb' (a '**' b)@ follows from @'TestOb' a@ and @'TestOb' b@). The @_@-suffixed
-- variant (e.g. 'testMonoidal_') supplies it from a 'TestObIsOb' constraint, for categories where
-- every object is a 'TestOb', typically those that leave 'TestOb' at its @'Ob'@ default.
module Proarrow.Testing.Laws where

import Control.Monad (unless, when)
import Data.Foldable (for_)
import Data.List (genericLength, sort)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (Property, genWith, testFailed, testProperty)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Adjunction (Adjunction)
import Proarrow.Category.Enriched.Dagger qualified as Dagger
import Proarrow.Category.Enriched.Finitary qualified as Finitary
import Proarrow.Category.Enriched.Finitary.Sheaf qualified as FinSheaf
import Proarrow.Category.Enriched.Finitary.Topos qualified as FinTopos
import Proarrow.Category.Enriched.Thin qualified as Thin
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (Sub (..))
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Cartesian qualified as Cartesian
import Proarrow.Category.Monoidal.Closed qualified as Exponential
import Proarrow.Category.Monoidal.CompactClosed qualified as CC
import Proarrow.Category.Monoidal.CopyDiscard qualified as CopyDiscard
import Proarrow.Category.Monoidal.Distributive qualified as Distributive
import Proarrow.Category.Monoidal.Hypergraph qualified as Hypergraph
import Proarrow.Category.Monoidal.StarAutonomous qualified as SA
import Proarrow.Category.Sheaf qualified as Sheaf
import Proarrow.Category.Topos qualified as Topos
import Proarrow.Colimit.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Colimit.Coequalizer qualified as Coequalizer
import Proarrow.Colimit.Initial qualified as Initial
import Proarrow.Colimit.Pushout qualified as Pushout
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), lmap, obj, rmap, (//), (:~>), type (+->))
import Proarrow.Functor qualified as Functor
import Proarrow.Limit.BinaryProduct qualified as BinaryProduct
import Proarrow.Limit.Equalizer qualified as Equalizer
import Proarrow.Limit.Pullback qualified as Pullback
import Proarrow.Limit.Terminal qualified as Terminal
import Proarrow.Monoid qualified as Monoid
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (ExOptic, Flip, Optic)
import Proarrow.Optic.Getter (GetterFl, review, view)
import Proarrow.Profunctor.Corepresentable
  ( Corepresentable
  , coindex
  , corepMap
  , cotabulate
  , withObCorep
  , type (%%)
  )
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))
import Proarrow.Profunctor.Representable (Rep, Representable, index, repMap, tabulate, withObRep, type (%))
import Proarrow.Testing
  ( Some (..)
  , SomeProfunctorElt (..)
  , TestOb'
  , TestObIsOb
  , Testable (..)
  , TestableProfunctor (..)
  , TestableTypeP
  , TestingEqShow (..)
  , expect
  , genNamed
  , genOb
  , genObSmall
  , genObSuchThat
  , genSuchThat
  , isGenNonEmpty
  , obFromTestOb
  , testEq
  )

-- * Objecthood witnesses

-- | How 'TestOb' is closed under the structure a law-checker is about.
--
-- Every @prop@\/@test@ below that needs one takes it as an explicit rank-2 argument, since in
-- general a category may make only some of its objects testable; the @_@-suffixed variants supply
-- the trivial witness. These synonyms only name the shapes, which would otherwise be spelled out
-- in forty-odd signatures.
type WithTestOb k = forall (a :: k) r. (Ob a) => ((TestOb a) => r) -> r

-- | @'TestOb'@ is closed under the tensor.
type WithTestOb2 k = forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a M.** b)) => r) -> r

-- | @'TestOb'@ is closed under the binary product.
type WithTestObProd k = forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a BinaryProduct.&& b)) => r) -> r

-- | @'TestOb'@ is closed under the binary coproduct.
type WithTestObCoprod k = forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a BinaryCoproduct.|| b)) => r) -> r

-- | @'TestOb'@ is closed under the internal hom.
type WithTestObExp k = forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a Exponential.~~> b)) => r) -> r

-- | @'TestOb'@ is closed under dualization.
type WithTestObDual k = forall (a :: k) r. (TestOb a) => ((TestOb (SA.Dual a)) => r) -> r

-- | @'TestOb'@ is closed under a representable profunctor.
type WithTestObRep k p = forall (a :: k) r. (TestOb a) => ((TestOb (p % a)) => r) -> r

-- | @'TestOb'@ is closed under a corepresentable profunctor.
type WithTestObCorep k p = forall (a :: k) r. (TestOb a) => ((TestOb (p %% a)) => r) -> r

-- * Isomorphisms

-- | Two arrows are mutually inverse: @f . g = id@ and @g . f = id@.
propIso :: forall {k} (a :: k) b. (Testable k, TestOb a, TestOb b) => a ~> b -> b ~> a -> Property ()
propIso f g = do
  testEq "right inverse" "f . g" (f . g) "id" id
  testEq "left inverse" "g . f" (g . f) "id" id

-- | An optic is an isomorphism: its 'view' and 'review' are mutually inverse, by 'propIso'.
propIso'
  :: forall {k} c (a :: k) b
   . (Testable k, TestOb a, TestOb b, (Ob b) => c (ExOptic GetterFl b b), (Ob b) => c (ExOptic (Flip GetterFl) b b))
  => Optic c a a b b -> Property ()
propIso' o = propIso (view o) (review o)

-- | Two functions between the elements of @p a b@ and of @q c d@ are mutually inverse, at
-- generated elements.
propIsoP
  :: forall p q a b c d
   . (TestableTypeP p, TestableTypeP q, TestOb a, TestOb b, TestOb c, TestOb d)
  => (p a b -> q c d) -> (q c d -> p a b) -> Property ()
propIsoP f g = do
  p <- genNamed @(p a b) "p"
  testEq "left inverse" "g (f p)" (g (f p)) "p" p
  q <- genNamed @(q c d) "q"
  testEq "right inverse" "f (g q)" (f (g q)) "q" q

-- | Two natural transformations are mutually inverse: 'propIsoP' at generated objects, and each is
-- natural ('propNaturalTransformation').
propNaturalIsoP
  :: forall {j} {k} (p :: j +-> k) q
   . (TestableProfunctor p, TestableTypeP p, TestableProfunctor q, TestableTypeP q)
  => (p :~> q) -> (q :~> p) -> Property ()
propNaturalIsoP f g = do
  Some @a <- genOb @k
  Some @b <- genOb @j
  propIsoP @p @q @a @b f g
  propNaturalTransformation f
  propNaturalTransformation g

-- * Categories

-- | The category laws: 'id' is a left and right identity for @(.)@, and @(.)@ is associative.
testCategory :: forall k. (Testable k) => TestTree
testCategory = testProperty "Category" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genNamed @(a ~> b) "f"
  testEq "left identity" "id . f" (id . f) "f" f
  testEq "right identity" "f . id" (f . id) "f" f
  Some @c <- genOb
  Some @d <- genOb
  g <- genNamed @(b ~> c) "g"
  h <- genNamed @(c ~> d) "h"
  testEq "associativity" "(h . g) . f" ((h . g) . f) "h . (g . f)" (h . (g . f))

-- | Laws of a dagger category: 'Dagger.dagger' is an identity-on-objects involution, and a
-- contravariant functor. Being identity-on-objects, it needs no objecthood witness: the dagger of
-- an @a '~>' b@ is a @b '~>' a@, never landing on a new object.
testDagger :: forall k. (Testable k, Dagger.Dagger k) => TestTree
testDagger = testProperty "Dagger" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  f <- genNamed @(a ~> b) "f"
  g <- genNamed @(b ~> c) "g"
  testEq "involution" "dagger (dagger f)" (Dagger.dagger (Dagger.dagger f)) "f" f
  testEq "identity" "dagger id" (Dagger.dagger (id :: a ~> a)) "id" (id :: a ~> a)
  testEq
    "contravariant"
    "dagger (g . f)"
    (Dagger.dagger (g . f))
    "dagger f . dagger g"
    (Dagger.dagger f . Dagger.dagger g)

-- * Profunctors

-- | The profunctor laws of @p@ ('propProfunctor') as a ready-made test.
testProfunctor :: forall {j} {k} (p :: j +-> k). (TestableProfunctor p) => TestTree
testProfunctor = testProperty "Profunctor" (propProfunctor @p)

-- | The profunctor laws of @p@ at elements from its 'TestableProfunctor' generator; see
-- 'propProfunctorWith'.
propProfunctor :: forall {j} {k} (p :: j +-> k). (TestableProfunctor p) => Property ()
propProfunctor = propProfunctorWith @p (genProfunctorElt "p") (\r -> r)

-- | The profunctor laws (@'dimap' id id = id@, 'lmap' and 'rmap' commute, and 'dimap' respects
-- composition) at elements drawn from the given generator, compared through the given
-- 'TestingEqShow' witness. For a profunctor whose elements are not a 'TestableProfunctor' of their
-- own, such as 'testClosed'\'s exponential.
propProfunctorWith
  :: forall {j} {k} (p :: j +-> k)
   . (Profunctor p, Testable j, Testable k)
  => Property (SomeProfunctorElt p)
  -> (forall a b r. (TestOb a, TestOb b) => ((TestingEqShow (p a b)) => r) -> r)
  -> Property ()
propProfunctorWith genPro withEqShow = do
  SomeP @a @b p <- genPro
  withEqShow @a @b $
    testEq "identity" "dimap id id p" (dimap id id p) "p" p
  Some @c <- genObSuchThat @k \(Some @c) -> isGenNonEmpty @(c ~> a)
  Some @d <- genObSuchThat @j \(Some @d) -> isGenNonEmpty @(b ~> d)
  f <- genNamed @(c ~> a) "f"
  g <- genNamed @(b ~> d) "g"
  withEqShow @c @d $
    testEq "interchange" "lmap f (rmap g p)" (lmap f (rmap g p)) "rmap g (lmap f p)" (rmap g (lmap f p))
  Some @e <- genObSuchThat @k \(Some @e) -> isGenNonEmpty @(e ~> c)
  Some @h <- genObSuchThat @j \(Some @h) -> isGenNonEmpty @(d ~> h)
  f' <- genNamed @(e ~> c) "f'"
  g' <- genNamed @(d ~> h) "g'"
  withEqShow @e @h $
    testEq
      "composition"
      "dimap (f . f') (g' . g) p"
      (dimap (f . f') (g' . g) p)
      "dimap f' g' (dimap f g p)"
      (dimap f' g' (dimap f g p))

-- | 'Thin.decide' agrees with the generator: an element of @p a b@ can be generated exactly
-- when @'Thin.Holds' p a b@ decides to 'Proarrow.Category.Instance.Bool.TRU', and then (the
-- profunctor being thin) it is the decided element.
propDecidable
  :: forall {j} {k} (p :: j +-> k)
   . (Thin.DecidableProfunctor p, Testable j, Testable k, TestableTypeP p)
  => Property ()
propDecidable = do
  Some @a <- genOb @k
  Some @b <- genOb @j
  obFromTestOb @a $
    obFromTestOb @b $
      case Thin.decide @p @a @b of
        Thin.Yes x -> do
          unless (isGenNonEmpty @(p a b)) $ testFailed "decide: TRU, but no element can be generated"
          y <- genNamed @(p a b) "y"
          testEq "decide" "decide" x "y" y
        Thin.No -> when (isGenNonEmpty @(p a b)) $ testFailed "decide: FLS, but an element can be generated"

-- | A transformation @n :: p ':~>' q@ is natural: @n ('dimap' f g p) = 'dimap' f g (n p)@.
propNaturalTransformation
  :: forall {j} {k} (p :: j +-> k) q. (TestableProfunctor p, TestableProfunctor q) => p :~> q -> Property ()
propNaturalTransformation n = do
  SomeP @a @b p <- genProfunctorElt @p "p"
  -- as in 'propProfunctorWith': an object with no arrow to @a@ discards the run
  Some @c <- genObSuchThat @k \(Some @c) -> isGenNonEmpty @(c ~> a)
  Some @d <- genObSuchThat @j \(Some @d) -> isGenNonEmpty @(b ~> d)
  f <- genNamed @(c ~> a) "f"
  g <- genNamed @(b ~> d) "g"
  testEq "naturality" "n (dimap f g p)" (n (dimap f g p)) "dimap f g (n p)" (dimap f g (n p))

-- | The numbering laws of a 'Finitary.Finitary' profunctor: 'Finitary.elements' has
-- 'Finitary.size' entries and is numbered in order, and 'Finitary.fromIndex' recovers any element
-- from its index, including elements the instance did not itself produce. That last law checks
-- that 'Finitary.size' is correct and not merely self-consistent, but only as far as the
-- 'TestableType' generator is independent of the instance. One defined as
-- @optGen 'Finitary.elements'@ makes it vacuous. The label names the profunctor, which nothing in
-- its type can supply.
testFinitary
  :: forall {j} {k} (p :: j +-> k)
   . (Testable j, Testable k, Finitary.Finitary p, TestableTypeP p)
  => String
  -> TestTree
testFinitary nm = testProperty ("Finitary " ++ nm) $ do
  Some @a <- genOb @k
  Some @b <- genOb @j
  let n = Finitary.size @p @a @b
      es = Finitary.elements @p @a @b
  unless (genericLength es == n) $
    testFailed ("size is " ++ show n ++ " but elements has " ++ show (genericLength es :: Natural) ++ " entries")
  unless (map (Finitary.toIndex @p @a @b) es == Finitary.indices n) $
    testFailed ("elements should be numbered in order, found " ++ show (map (Finitary.toIndex @p @a @b) es))
  x <- genNamed @(p a b) "x"
  -- The numbering claims every index is below 'Finitary.size', which a @Fin@-typed index would
  -- have given for free. Without this check an undersized 'Finitary.size' goes unnoticed, since
  -- the other laws only ever look at the elements it admits.
  unless (Finitary.toIndex x < n) $
    testFailed ("toIndex " ++ showP x ++ " is " ++ show (Finitary.toIndex x) ++ ", not below size " ++ show n)
  roundTrips <- eqP (Finitary.fromIndex @p @a @b (Finitary.toIndex x)) x
  unless roundTrips $ testFailed ("fromIndex (toIndex x) /= x for x = " ++ showP x)

-- * Functors, representability and adjunctions

-- | Check the functor laws of a 'Functor.Functor' @f@: @map id = id@ and @map (g . f) = map g . map
-- f@. The witness lifts 'TestOb' along @f@ (usually @\\ \@a r -> r@ when @'TestOb' (f a)@ follows
-- from @'TestOb' a@). Functors encoded as representable profunctors ('Functor.FunctorForRep') are
-- instead tested via their @'Proarrow.Profunctor.Representable.Rep'@ with 'propProfunctor', since
-- the profunctor laws on @Rep f@ are the functor laws on @f@.
propFunctor
  :: forall {k1} {k2} (f :: k1 -> k2)
   . (Functor.Functor f, Testable k1, Testable k2)
  => (forall (a :: k1) r. (TestOb a) => ((TestOb (f a)) => r) -> r)
  -> Property ()
propFunctor withTestObF = do
  Some @a <- genOb @k1
  Some @b <- genObSuchThat @k1 \(Some @b) -> isGenNonEmpty @(a ~> b)
  Some @c <- genObSuchThat @k1 \(Some @c) -> isGenNonEmpty @(b ~> c)
  f <- genNamed @(a ~> b) "f"
  g <- genNamed @(b ~> c) "g"
  withTestObF @a $
    withTestObF @c $
      -- 'Functor.withObF' recovers @Ob (f a)@\/@Ob (f c)@ from the functor (GHC will not extract
      -- them from the quantified @Ob' (f a)@ superclass on its own)
      Functor.withObF @f @a $
        Functor.withObF @f @c $ do
          testEq "identity" "map id" (Functor.map @f (obj @a)) "id" (obj @(f a))
          testEq
            "composition"
            "map (g . f)"
            (Functor.map @f (g . f))
            "map g . map f"
            (Functor.map @f g . Functor.map @f f)

-- | The functor laws of @f@ ('propFunctor') as a ready-made test.
testFunctor
  :: forall {k1} {k2} (f :: k1 -> k2)
   . (Functor.Functor f, Testable k1, Testable k2)
  => (forall (a :: k1) r. (TestOb a) => ((TestOb (f a)) => r) -> r)
  -> TestTree
testFunctor withTestObF = testProperty "Functor" (propFunctor @f (\ @a r -> withTestObF @a r))

testFunctor_
  :: forall {k1} {k2} (f :: k1 -> k2)
   . (Functor.Functor f, Testable k1, Testable k2, forall (a :: k1). (TestOb a) => TestOb' (f a))
  => TestTree
testFunctor_ = testFunctor @f (\r -> r)

-- | Check the 'Representable' laws of @p@: 'index' and 'tabulate' are mutually inverse (@p a b@ is
-- naturally isomorphic to @a '~>' p '%' b@), and that iso is natural,
-- @'index' ('dimap' f g p) = 'repMap' g '.' 'index' p '.' f@, which pins 'repMap' down as
-- the functorial action of the representing functor @p '%' -@. The witness lifts 'TestOb' along
-- @p '%' -@. Unlike the hom-level 'propAdjunction', this generates @p a b@ elements, so it needs @p@
-- to be an element-generatable 'TestableProfunctor'.
propRepresentable
  :: forall {j} {k} (p :: j +-> k)
   . (Representable p, TestableProfunctor p)
  => WithTestObRep j p
  -> Property ()
propRepresentable withTestObRep = do
  SomeP @a @b p <- genProfunctorElt @p "p"
  testEq "tabulate . index" "tabulate (index p)" (tabulate @p (index p)) "p" p
  withTestObRep @b @(Property ()) do
    f <- genNamed @(a ~> p % b) "f"
    testEq "index . tabulate" "index (tabulate f)" (index @p (tabulate @p @b @a f)) "f" f
  Some @c <- genObSuchThat @k \(Some @c) -> isGenNonEmpty @(c ~> a)
  Some @d <- genObSuchThat @j \(Some @d) -> isGenNonEmpty @(b ~> d)
  fc <- genNamed @(c ~> a) "f"
  gd <- genNamed @(b ~> d) "g"
  withTestObRep @d @(Property ()) do
    testEq
      "index naturality"
      "index (dimap f g p)"
      (index @p (dimap fc gd p))
      "repMap g . index p . f"
      (repMap @p gd . index @p p . fc)

-- | The 'Representable' laws of @p@ ('propRepresentable') as a ready-made test.
testRepresentable
  :: forall {j} {k} (p :: j +-> k)
   . (Representable p, TestableProfunctor p)
  => WithTestObRep j p
  -> TestTree
testRepresentable withTestObRep = testProperty "Representable" (propRepresentable @p (\ @b r -> withTestObRep @b r))

testRepresentable_ :: forall {j} {k} (p :: j +-> k). (Representable p, TestableProfunctor p, TestObIsOb k) => TestTree
testRepresentable_ = testRepresentable @p (\ @b r -> withObRep @p @b r)

-- | Check the 'Corepresentable' laws of @p@, dual to 'propRepresentable': 'coindex' and 'cotabulate'
-- are mutually inverse (@p a b@ is naturally isomorphic to @p '%%' a '~>' b@), and that iso is
-- natural, @'coindex' ('dimap' f g p) = g '.' 'coindex' p '.' 'corepMap' f@, pinning down 'corepMap'
-- as the functorial action of the corepresenting functor @p '%%' -@. The witness lifts 'TestOb' along
-- @p '%%' -@.
propCorepresentable
  :: forall {j} {k} (p :: j +-> k)
   . (Corepresentable p, TestableProfunctor p)
  => WithTestObCorep k p
  -> Property ()
propCorepresentable withTestObCorep = do
  SomeP @a @b p <- genProfunctorElt @p "p"
  testEq "cotabulate . coindex" "cotabulate (coindex p)" (cotabulate @p (coindex p)) "p" p
  withTestObCorep @a @(Property ()) do
    f <- genNamed @(p %% a ~> b) "f"
    testEq "coindex . cotabulate" "coindex (cotabulate f)" (coindex @p (cotabulate @p @a @b f)) "f" f
  Some @c <- genObSuchThat @k \(Some @c) -> isGenNonEmpty @(c ~> a)
  Some @d <- genObSuchThat @j \(Some @d) -> isGenNonEmpty @(b ~> d)
  fc <- genNamed @(c ~> a) "f"
  gd <- genNamed @(b ~> d) "g"
  withTestObCorep @c @(Property ()) do
    testEq
      "coindex naturality"
      "coindex (dimap f g p)"
      (coindex @p (dimap fc gd p))
      "g . coindex p . corepMap f"
      (gd . coindex @p p . corepMap @p fc)

-- | The 'Corepresentable' laws of @p@ ('propCorepresentable') as a ready-made test.
testCorepresentable
  :: forall {j} {k} (p :: j +-> k)
   . (Corepresentable p, TestableProfunctor p)
  => WithTestObCorep k p
  -> TestTree
testCorepresentable withTestObCorep = testProperty "Corepresentable" (propCorepresentable @p (\ @a r -> withTestObCorep @a r))

testCorepresentable_
  :: forall {j} {k} (p :: j +-> k)
   . (Corepresentable p, TestableProfunctor p, TestObIsOb j)
  => TestTree
testCorepresentable_ = testCorepresentable @p (\ @a r -> withObCorep @p @a r)

-- | Check the adjunction laws of an 'Adjunction' @p@. An adjunction here is a profunctor that is
-- both 'Representable' and 'Corepresentable', with left adjoint @L = p '%%' -@ and right adjoint
-- @R = p '%' -@. It carries no laws of its own beyond theirs ('leftAdjunct'\/'rightAdjunct' are just
-- @'index' '.' 'cotabulate'@ and @'coindex' '.' 'tabulate'@), so this delegates to
-- 'propCorepresentable' (for @L@) and 'propRepresentable' (for @R@). The two witnesses lift 'TestOb'
-- along @L@ and @R@ respectively.
propAdjunction
  :: forall {j} {k} (p :: j +-> k)
   . (Adjunction p, TestableProfunctor p)
  => WithTestObCorep k p
  -> WithTestObRep j p
  -> Property ()
propAdjunction withTestObL withTestObR = do
  propCorepresentable @p (\ @a r -> withTestObL @a r)
  propRepresentable @p (\ @b r -> withTestObR @b r)

-- | The laws of the adjunction @p@ ('propAdjunction') as a ready-made test.
testAdjunction
  :: forall {j} {k} (p :: j +-> k)
   . (Adjunction p, TestableProfunctor p)
  => WithTestObCorep k p
  -> WithTestObRep j p
  -> TestTree
testAdjunction withTestObL withTestObR =
  testProperty "Adjunction" (propAdjunction @p (\ @a r -> withTestObL @a r) (\ @b r -> withTestObR @b r))

testAdjunction_
  :: forall {j} {k} (p :: j +-> k)
   . (Adjunction p, TestableProfunctor p, TestObIsOb j, TestObIsOb k)
  => TestTree
testAdjunction_ = testAdjunction @p (\ @a r -> withObCorep @p @a r) (\ @b r -> withObRep @p @b r)

-- * Limits and colimits

-- | Every arrow into the 'Terminal.TerminalObject' is 'Terminal.terminate'.
testTerminalObject
  :: forall k
   . (Testable k, Terminal.HasTerminalObject k, TestOb (Terminal.TerminalObject :: k))
  => TestTree
testTerminalObject = testProperty "Terminal object" $ do
  Some @a <- genOb @k
  g <- genNamed @(a ~> Terminal.TerminalObject) "g"
  testEq "uniqueness" "g" g "terminate" Terminal.terminate

-- | Every arrow out of the 'Initial.InitialObject' is 'Initial.initiate'.
testInitialObject :: forall k. (Testable k, Initial.HasInitialObject k, TestOb (Initial.InitialObject :: k)) => TestTree
testInitialObject = testProperty "Initial object" $ do
  Some @a <- genOb @k
  g <- genNamed @(Initial.InitialObject ~> a) "g"
  testEq "uniqueness" "g" g "initiate" Initial.initiate

-- | The universal property of the binary product: the projections recover the components of
-- @f '&&&' g@, and pairing commutes with precomposition, which with the first two makes it unique.
testBinaryProducts :: forall k. (Testable k, BinaryProduct.HasBinaryProducts k) => WithTestObProd k -> TestTree
testBinaryProducts withTestObProd = testProperty "Binary products" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  Some @z <- genOb
  withTestObProd @b @c $ do
    f <- genNamed @(a ~> b) "f"
    g <- genNamed @(a ~> c) "g"
    testEq "fst" "fst . (f &&& g)" (BinaryProduct.fst @k @b @c . (f BinaryProduct.&&& g)) "f" f
    testEq "snd" "snd . (f &&& g)" (BinaryProduct.snd @k @b @c . (f BinaryProduct.&&& g)) "g" g
    h <- genNamed @(z ~> a) "h"
    testEq
      "uniqueness"
      "(f . h) &&& (g . h)"
      ((f . h) BinaryProduct.&&& (g . h))
      "(f &&& g) . h"
      ((f BinaryProduct.&&& g) . h)

testBinaryProducts_ :: forall k. (Testable k, BinaryProduct.HasBinaryProducts k, TestObIsOb k) => TestTree
testBinaryProducts_ = testBinaryProducts @k (\ @a @b r -> BinaryProduct.withObProd @k @a @b r)

-- | The universal property of the binary coproduct, dual to 'testBinaryProducts': the injections
-- recover the components of @f '|||' g@, and copairing commutes with postcomposition.
testBinaryCoproducts :: forall k. (Testable k, BinaryCoproduct.HasBinaryCoproducts k) => WithTestObCoprod k -> TestTree
testBinaryCoproducts withTestObCoprod = testProperty "Binary coproducts" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  Some @z <- genOb
  withTestObCoprod @a @b $ do
    f <- genNamed @(a ~> c) "f"
    g <- genNamed @(b ~> c) "g"
    testEq "lft" "(f ||| g) . lft" ((f BinaryCoproduct.||| g) . BinaryCoproduct.lft @k @a @b) "f" f
    testEq "rgt" "(f ||| g) . rgt" ((f BinaryCoproduct.||| g) . BinaryCoproduct.rgt @k @a @b) "g" g
    h <- genNamed @(c ~> z) "h"
    testEq
      "uniqueness"
      "(h . f) ||| (h . g)"
      ((h . f) BinaryCoproduct.||| (h . g))
      "h . (f ||| g)"
      (h . (f BinaryCoproduct.||| g))

testBinaryCoproducts_ :: forall k. (Testable k, BinaryCoproduct.HasBinaryCoproducts k, TestObIsOb k) => TestTree
testBinaryCoproducts_ = testBinaryCoproducts @k (\ @a @b r -> BinaryCoproduct.withObCoprod @k @a @b r)

-- | Check that composing with an arrow /reflects/ equality: the composites agree exactly when the
-- two arrows already did. @eqComposed@ is the caller\'s comparison of the composites (a
-- conjunction, where two projections have to be checked together), and @desc@ names it for the
-- failure message.
--
-- This is the mono half of an equalizer, the epi half of a coequalizer, and the jointly-monic and
-- jointly-epic halves of a pullback and a pushout.
propReflectsEq :: (TestingEqShow x) => String -> String -> Bool -> x -> x -> Property ()
propReflectsEq label desc eqComposed k1 k2 = do
  eqDirect <- eqP k1 k2
  unless (eqComposed == eqDirect) $
    testFailed $
      "Failed " ++ label ++ ": (" ++ desc ++ ") = " ++ show eqComposed ++ " but (k1 == k2) = " ++ show eqDirect

-- | Checks the equalizer laws: the equalizer arrow @e@ equalizes @f@ and @g@; any @h@ that factors
-- through @e@ (generated as @e . p@) is recovered by 'Equalizer.factorEqualizer'; and @e@ is mono.
--
-- The equalizer object is not computed by a type family, so its 'Ob' comes from the arrow via
-- 'Objs', and @withTestOb@ only has to bridge that one 'Ob' to 'TestOb'.
testEqualizers :: forall k. (Testable k, Equalizer.HasEqualizers k) => WithTestOb k -> TestTree
testEqualizers withTestOb = testProperty "Equalizers" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genNamed @(a ~> b) "f"
  g <- genNamed @(a ~> b) "g"
  Equalizer.equalize f g \ @e ee@Objs -> withTestOb @e $ do
    testEq "equalizing" "f . e" (f . ee) "g . e" (g . ee)
    Some @z <- genOb
    p <- genNamed @(z ~> e) "p"
    let h = ee . p
        factored = Equalizer.factorEqualizer ee h
    testEq "factorization" "e . factored" (ee . factored) "h" h
    -- The half the constructed @h@ cannot reach: an /arbitrary/ arrow that happens to equalize
    -- must factor too. Without it an undersized equalizer (one keeping too few elements)
    -- satisfies everything above, since every arrow it is ever handed was built through it.
    m <- genNamed @(z ~> a) "m"
    equalizes <- eqP (f . m) (g . m)
    when equalizes $
      testEq "existence" "e . factorEqualizer e m" (ee . Equalizer.factorEqualizer ee m) "m" m
    k1 <- genNamed @(z ~> e) "k1"
    k2 <- genNamed @(z ~> e) "k2"
    eqComposed <- eqP (ee . k1) (ee . k2)
    propReflectsEq "mono" "e . k1 == e . k2" eqComposed k1 k2

testEqualizers_ :: forall k. (Testable k, Equalizer.HasEqualizers k, TestObIsOb k) => TestTree
testEqualizers_ = testEqualizers @k (\r -> r)

-- | Checks the coequalizer laws, dual to 'testEqualizers': the coequalizer arrow @c@ coequalizes @f@
-- and @g@; any @h@ that factors through @c@ (built here as @p . c@ for an arbitrary @p@, so the
-- precondition holds by construction) is correctly recovered by 'Coequalizer.factorCoequalizer'; and
-- @c@ is epi (post-composing with it on the right reflects equality).
testCoequalizers :: forall k. (Testable k, Coequalizer.HasCoequalizers k) => WithTestOb k -> TestTree
testCoequalizers withTestOb = testProperty "Coequalizers" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genNamed @(a ~> b) "f"
  g <- genNamed @(a ~> b) "g"
  Coequalizer.coequalize f g \ @c cq@Objs -> withTestOb @c $ do
    testEq "coequalizing" "c . f" (cq . f) "c . g" (cq . g)
    Some @z <- genOb
    p <- genNamed @(c ~> z) "p"
    let h = p . cq
        factored = Coequalizer.factorCoequalizer cq h
    testEq "factorization" "factored . c" (factored . cq) "h" h
    -- As in 'testEqualizers': an arbitrary arrow that coequalizes must factor, not only one
    -- built by composing through @cq@.
    m <- genNamed @(b ~> z) "m"
    coequalizes <- eqP (m . f) (m . g)
    when coequalizes $
      testEq "existence" "factorCoequalizer c m . c" (Coequalizer.factorCoequalizer cq m . cq) "m" m
    k1 <- genNamed @(c ~> z) "k1"
    k2 <- genNamed @(c ~> z) "k2"
    eqComposed <- eqP (k1 . cq) (k2 . cq)
    propReflectsEq "epi" "k1 . c == k2 . c" eqComposed k1 k2

testCoequalizers_ :: forall k. (Testable k, Coequalizer.HasCoequalizers k, TestObIsOb k) => TestTree
testCoequalizers_ = testCoequalizers @k (\r -> r)

-- | Checks the pullback laws: the pullback cone commutes; it's jointly monic (composing with both
-- legs at once reflects equality); and any compatible cone (built here as @(p1 . j, p2 . j)@ for an
-- arbitrary @j@, so compatibility holds by construction) is correctly recovered by
-- 'Pullback.factorPullback'.
testPullbacks :: forall k. (Testable k, Pullback.HasPullbacks k) => WithTestOb k -> TestTree
testPullbacks withTestOb = testProperty "Pullbacks" $ do
  Some @o <- genOb @k
  Some @a <- genOb
  Some @b <- genOb
  f <- genNamed @(a ~> o) "f"
  g <- genNamed @(b ~> o) "g"
  Pullback.pullback f g \ @p p1@Objs p2 -> withTestOb @p $ do
    testEq "commutes" "f . p1" (f . p1) "g . p2" (g . p2)
    Some @z <- genOb
    k1' <- genNamed @(z ~> p) "k1"
    k2' <- genNamed @(z ~> p) "k2"
    eq1 <- eqP (p1 . k1') (p1 . k2')
    eq2 <- eqP (p2 . k1') (p2 . k2')
    propReflectsEq "jointly monic" "p1 . k1 == p1 . k2 && p2 . k1 == p2 . k2" (eq1 && eq2) k1' k2'
    j <- genNamed @(z ~> p) "j"
    let k1 = p1 . j
        k2 = p2 . j
        factored = Pullback.factorPullback p1 p2 k1 k2
    testEq "factorization (1)" "p1 . factored" (p1 . factored) "k1" k1
    testEq "factorization (2)" "p2 . factored" (p2 . factored) "k2" k2
    -- And the half those cannot reach: an arbitrary commuting cone must factor too.
    x <- genNamed @(z ~> a) "x"
    y <- genNamed @(z ~> b) "y"
    commutes <- eqP (f . x) (g . y)
    when commutes $ do
      let fac = Pullback.factorPullback p1 p2 x y
      testEq "existence (1)" "p1 . factorPullback p1 p2 x y" (p1 . fac) "x" x
      testEq "existence (2)" "p2 . factorPullback p1 p2 x y" (p2 . fac) "y" y

testPullbacks_ :: forall k. (Testable k, Pullback.HasPullbacks k, TestObIsOb k) => TestTree
testPullbacks_ = testPullbacks @k (\r -> r)

-- | Checks the pushout laws, dual to 'testPullbacks': the pushout cocone commutes; it's jointly epic
-- (post-composing with both legs at once reflects equality); and any compatible cocone (built here as
-- @(j . p1, j . p2)@ for an arbitrary @j@, so compatibility holds by construction) is correctly
-- recovered by 'Pushout.factorPushout'.
testPushouts :: forall k. (Testable k, Pushout.HasPushouts k) => WithTestOb k -> TestTree
testPushouts withTestOb = testProperty "Pushouts" $ do
  Some @o <- genOb @k
  Some @a <- genOb
  Some @b <- genOb
  f <- genNamed @(o ~> a) "f"
  g <- genNamed @(o ~> b) "g"
  Pushout.pushout f g \ @p p1@Objs p2 -> withTestOb @p $ do
    testEq "commutes" "p1 . f" (p1 . f) "p2 . g" (p2 . g)
    Some @z <- genOb
    k1' <- genNamed @(p ~> z) "k1"
    k2' <- genNamed @(p ~> z) "k2"
    eq1 <- eqP (k1' . p1) (k2' . p1)
    eq2 <- eqP (k1' . p2) (k2' . p2)
    propReflectsEq "jointly epic" "k1 . p1 == k2 . p1 && k1 . p2 == k2 . p2" (eq1 && eq2) k1' k2'
    j <- genNamed @(p ~> z) "j"
    let k1 = j . p1
        k2 = j . p2
        factored = Pushout.factorPushout p1 p2 k1 k2
    testEq "factorization (1)" "factored . p1" (factored . p1) "k1" k1
    testEq "factorization (2)" "factored . p2" (factored . p2) "k2" k2
    -- And the half those cannot reach: an arbitrary commuting cocone must factor too.
    x <- genNamed @(a ~> z) "x"
    y <- genNamed @(b ~> z) "y"
    commutes <- eqP (x . f) (y . g)
    when commutes $ do
      let fac = Pushout.factorPushout p1 p2 x y
      testEq "existence (1)" "factorPushout p1 p2 x y . p1" (fac . p1) "x" x
      testEq "existence (2)" "factorPushout p1 p2 x y . p2" (fac . p2) "y" y

testPushouts_ :: forall k. (Testable k, Pushout.HasPushouts k, TestObIsOb k) => TestTree
testPushouts_ = testPushouts @k (\r -> r)

-- | Checks the epi-mono factorization laws: 'Topos.factorize' splits @f@ as @m . e@ through an
-- image object, with @e@ epi and @m@ mono.
--
-- As with 'testEqualizers' the image object is revealed at runtime rather than computed by a type
-- family, so @withTestOb@ bridges its recovered 'Ob' to 'TestOb'. The epi and mono halves are the
-- two directions of 'propReflectsEq': composing on the right with @e@, and on the left with @m@.
testEpiMonoFactorization
  :: forall k. (Testable k, Topos.HasEpiMonoFactorization k) => WithTestOb k -> TestTree
testEpiMonoFactorization withTestOb = testProperty "Epi-mono factorization" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genNamed @(a ~> b) "f"
  case Topos.factorize f of
    (:.:) @x e@Objs m -> withTestOb @x $ do
      testEq "factorization" "m . e" (m . e) "f" f
      Some @z <- genOb
      k1 <- genNamed @(x ~> z) "k1"
      k2 <- genNamed @(x ~> z) "k2"
      eqEpi <- eqP (k1 . e) (k2 . e)
      propReflectsEq "epi" "k1 . e == k2 . e" eqEpi k1 k2
      j1 <- genNamed @(z ~> x) "k1"
      j2 <- genNamed @(z ~> x) "k2"
      eqMono <- eqP (m . j1) (m . j2)
      propReflectsEq "mono" "m . k1 == m . k2" eqMono j1 j2

testEpiMonoFactorization_
  :: forall k. (Testable k, Topos.HasEpiMonoFactorization k, TestObIsOb k) => TestTree
testEpiMonoFactorization_ = testEpiMonoFactorization @k (\r -> r)

-- * Monoidal structure

-- | The monoidal laws, split so that each half only establishes the objecthood it uses: the
-- unitors and the triangle need seven instances of @withTestOb2@, the associator and the pentagon
-- the other twelve.
testMonoidal :: forall k. (Testable k, M.Monoidal k, TestOb (M.Unit @k)) => WithTestOb2 k -> TestTree
testMonoidal withTestOb2 =
  testGroup
    "Monoidal"
    [ testProperty "unitors" $ do
        Some @a <- genOb @k
        Some @b <- genOb
        f <- genNamed @(a ~> b) "f"
        withTestOb2 @a @b $
          withTestOb2 @M.Unit @a $
            withTestOb2 @M.Unit @b $
              withTestOb2 @a @M.Unit $
                withTestOb2 @b @M.Unit $
                  withTestOb2 @a @(M.Unit M.** b) $
                    withTestOb2 @(a M.** M.Unit) @b $ do
                      propIso (M.leftUnitor @k @a) (M.leftUnitorInv @k @a)
                      propIso (M.rightUnitor @k @a) (M.rightUnitorInv @k @a)
                      testEq
                        "leftUnitor naturality"
                        "leftUnitor . (one ** f)"
                        (M.leftUnitor @k @b . (obj @M.Unit M.** f))
                        "f . leftUnitor"
                        (f . M.leftUnitor @k @a)
                      testEq
                        "leftUnitorInv naturality"
                        "leftUnitorInv . f"
                        (M.leftUnitorInv @k @b . f)
                        "(one ** f) . leftUnitorInv"
                        ((obj @M.Unit M.** f) . M.leftUnitorInv @k @a)
                      testEq
                        "rightUnitor naturality"
                        "rightUnitor . (f ** one)"
                        (M.rightUnitor @k @b . (f M.** obj @M.Unit))
                        "f . rightUnitor"
                        (f . M.rightUnitor @k @a)
                      testEq
                        "rightUnitorInv naturality"
                        "rightUnitorInv . f"
                        (M.rightUnitorInv @k @b . f)
                        "(f ** one) . rightUnitorInv"
                        ((f M.** obj @M.Unit) . M.rightUnitorInv @k @a)
                      testEq
                        "triangle identity"
                        "(id ** leftUnitor) . associator"
                        ((obj @a M.** M.leftUnitor @k @b) . M.associator @k @a @M.Unit @b)
                        "rightUnitor ** id"
                        (M.rightUnitor @k @a M.** obj @b)
    , testProperty "associator" $ do
        Some @a <- genOb @k
        Some @b <- genOb
        Some @c <- genOb
        Some @d <- genOb
        f <- genNamed @(a ~> b) "f"
        g <- genNamed @(b ~> c) "g"
        h <- genNamed @(c ~> d) "h"
        withTestOb2 @a @b $
          withTestOb2 @b @c $
            withTestOb2 @c @d $
              withTestOb2 @(a M.** b) @(c M.** d) $
                withTestOb2 @(a M.** b) @c $
                  withTestOb2 @a @(b M.** c) $
                    withTestOb2 @(a M.** (b M.** c)) @d $
                      withTestOb2 @(b M.** c) @d $
                        withTestOb2 @a @((b M.** c) M.** d) $
                          withTestOb2 @b @(c M.** d) $
                            withTestOb2 @a @(b M.** (c M.** d)) $
                              withTestOb2 @((a M.** b) M.** c) @d $ do
                                propIso (M.associator @k @a @b @c) (M.associatorInv @k @a @b @c)
                                testEq
                                  "associator naturality"
                                  "associator . ((f ** g) ** h)"
                                  (M.associator @k @b @c @d . ((f M.** g) M.** h))
                                  "(f ** (g ** h)) . associator"
                                  ((f M.** (g M.** h)) . M.associator @k @a @b @c)
                                testEq
                                  "associatorInv naturality"
                                  "associatorInv . (f ** (g ** h))"
                                  (M.associatorInv @k @b @c @d . (f M.** (g M.** h)))
                                  "((f ** g) ** h) . associatorInv"
                                  (((f M.** g) M.** h) . M.associatorInv @k @a @b @c)
                                testEq
                                  "pentagon identity"
                                  "(id ** associator) . associator . (associator ** id)"
                                  ( (obj @a M.** M.associator @k @b @c @d)
                                      . M.associator @k @a @(b M.** c) @d
                                      . (M.associator @k @a @b @c M.** obj @d)
                                  )
                                  "associator . associator"
                                  (M.associator @k @a @b @(c M.** d) . M.associator @k @(a M.** b) @c @d)
    ]

testMonoidal_ :: forall k. (Testable k, M.Monoidal k, TestObIsOb k) => TestTree
testMonoidal_ = testMonoidal @k (\ @a @b r -> M.withOb2 @k @a @b r)

-- | The laws of a symmetric monoidal category: 'M.swap' is its own inverse, and the hexagon
-- identity relating it to the associator.
testSymMonoidal :: forall k. (Testable k, M.SymMonoidal k, TestOb (M.Unit @k)) => WithTestOb2 k -> TestTree
testSymMonoidal withTestOb2 = testProperty "Symmetric monoidal" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  withTestOb2 @a @b $
    withTestOb2 @b @c $
      withTestOb2 @c @a $
        withTestOb2 @(a M.** b) @c $
          withTestOb2 @b @(c M.** a) $
            do
              testEq "swap swap" "swap . swap" (M.swap @k @b @a . M.swap @k @a @b) "id" id
              testEq
                "hexagon identity"
                "associator . swap . associator"
                (M.associator @k @b @c @a . M.swap @k @a @(b M.** c) . M.associator @k @a @b @c)
                "(swap ** id) . associator . (id ** swap)"
                ((obj @b M.** M.swap @k @a @c) . M.associator @k @b @a @c . (M.swap @k @a @b M.** obj @c))

testSymMonoidal_ :: forall k. (Testable k, M.SymMonoidal k, TestObIsOb k) => TestTree
testSymMonoidal_ = testSymMonoidal @k (\ @a @b r -> M.withOb2 @k @a @b r)

-- | Laws of a lax monoidal profunctor ('M.MonoidalProfunctor'): @'M.**'@ is natural in both
-- arguments and coherent with the unitors and the associator. For a monoidal category take
-- @p = 'Hom' k@; there naturality is bifunctoriality of the tensor,
-- @(g ** g\') . (f ** f\') == (g . f) ** (g\' . f\')@, which a /premonoidal/ @**@ fails while
-- passing 'testMonoidal'.
propMonoidalProfunctor
  :: forall {j} {k} (p :: j +-> k)
   . (M.MonoidalProfunctor p, TestableProfunctor p, TestOb (M.Unit @k), TestOb (M.Unit @j))
  => WithTestOb2 k
  -> WithTestOb2 j
  -> Property ()
propMonoidalProfunctor withTestObK withTestObJ = do
  SomeP @a @b x <- genProfunctorElt @p "x"
  SomeP @c @d y <- genProfunctorElt @p "y"
  withTestObK @a @c @(Property ()) $ withTestObJ @b @d @(Property ()) $ do
    Some @a' <- genObSuchThat @k \(Some @a') -> isGenNonEmpty @(a' ~> a)
    Some @c' <- genObSuchThat @k \(Some @c') -> isGenNonEmpty @(c' ~> c)
    l1 <- genNamed @(a' ~> a) "l1"
    l2 <- genNamed @(c' ~> c) "l2"
    withTestObK @a' @c' @(Property ()) $
      testEq
        "lmap naturality"
        "lmap (l1 ** l2) (x ** y)"
        (lmap (l1 M.** l2) (x M.** y))
        "lmap l1 x ** lmap l2 y"
        (lmap l1 x M.** lmap l2 y)
    Some @b' <- genObSuchThat @j \(Some @b') -> isGenNonEmpty @(b ~> b')
    Some @d' <- genObSuchThat @j \(Some @d') -> isGenNonEmpty @(d ~> d')
    r1 <- genNamed @(b ~> b') "r1"
    r2 <- genNamed @(d ~> d') "r2"
    withTestObJ @b' @d' @(Property ()) $
      testEq
        "rmap naturality"
        "rmap (r1 ** r2) (x ** y)"
        (rmap (r1 M.** r2) (x M.** y))
        "rmap r1 x ** rmap r2 y"
        (rmap r1 x M.** rmap r2 y)
    withTestObK @(M.Unit @k) @a @(Property ()) $
      withTestObJ @(M.Unit @j) @b @(Property ()) $
        testEq
          "left unit"
          "dimap leftUnitorInv leftUnitor (one ** x)"
          (dimap (M.leftUnitorInv @k @a) (M.leftUnitor @j @b) (M.one @p M.** x))
          "x"
          x
    withTestObK @a @(M.Unit @k) @(Property ()) $
      withTestObJ @b @(M.Unit @j) @(Property ()) $
        testEq
          "right unit"
          "dimap rightUnitorInv rightUnitor (x ** one)"
          (dimap (M.rightUnitorInv @k @a) (M.rightUnitor @j @b) (x M.** M.one @p))
          "x"
          x
    SomeP @e @f z <- genProfunctorElt @p "z"
    withTestObK @c @e @(Property ()) $
      withTestObJ @d @f @(Property ()) $
        withTestObK @a @(c M.** e) @(Property ()) $
          withTestObJ @b @(d M.** f) @(Property ()) $
            withTestObK @(a M.** c) @e @(Property ()) $
              withTestObJ @(b M.** d) @f @(Property ()) $
                testEq
                  "associativity"
                  "dimap associatorInv associator ((x ** y) ** z)"
                  (dimap (M.associatorInv @k @a @c @e) (M.associator @j @b @d @f) ((x M.** y) M.** z))
                  "x ** (y ** z)"
                  (x M.** (y M.** z))

-- | 'propMonoidalProfunctor' at a monoidal category\'s own hom-profunctor. The two kinds coincide
-- there, so one witness serves both.
testMonoidalHom :: forall k. (Testable k, M.Monoidal k, TestOb (M.Unit @k)) => WithTestOb2 k -> TestTree
-- Both witnesses are eta-expanded rather than passed through: 'TestOb' is an associated type
-- family, so two rank-2 witness types cannot be matched by unification, and each use has to be
-- solved at its own concrete objects.
testMonoidalHom withTestOb2 =
  testProperty
    "Monoidal profunctor"
    (propMonoidalProfunctor @(Hom k) (\ @a @b r -> withTestOb2 @a @b r) (\ @a @b r -> withTestOb2 @a @b r))

testMonoidalHom_ :: forall k. (Testable k, M.Monoidal k, TestObIsOb k, TestOb (M.Unit @k)) => TestTree
testMonoidalHom_ = testMonoidalHom @k (\ @a @b r -> M.withOb2 @k @a @b r)

-- | Every object is a cocommutative comonoid under 'CopyDiscard.copy' and 'CopyDiscard.discard'
-- ('propCocommutativeComonoid'). The first witness recovers the comonoid of an object from its
-- 'TestOb'.
testCopyDiscard
  :: forall k
   . (Testable k, CopyDiscard.CopyDiscard k, TestOb (M.Unit @k))
  => (forall (a :: k) r. (TestOb a) => ((Ob a, Monoid.CocommutativeComonoid a) => r) -> r)
  -> WithTestOb2 k
  -> TestTree
testCopyDiscard withCoco withTestOb2 = testProperty "CopyDiscard" $ do
  Some @a <- genOb @k
  withCoco @a (propCocommutativeComonoid @a (\ @x @y r -> withTestOb2 @x @y r))

-- | The cocommutative comonoid on each object is supplied by 'CopyDiscard.CopyDiscard' itself (its
-- @'Monoid.Supplies' 'Monoid.CocommutativeComonoid' k@ superclass), so only @'Ob' a@ has to be
-- recovered from @'TestOb' a@. That goes through 'obFromTestOb', because with that quantified
-- superclass in scope GHC does not find the @TestOb a => Ob' a => Ob a@ route on its own.
testCopyDiscard_ :: forall k. (Testable k, CopyDiscard.CopyDiscard k, TestObIsOb k) => TestTree
testCopyDiscard_ =
  testCopyDiscard @k (\ @a r -> obFromTestOb @a r) (\ @a @b r -> obFromTestOb @a (obFromTestOb @b (M.withOb2 @k @a @b r)))

-- | The coherence law tying 'Cartesian.Cartesian' to its 'CopyDiscard.CopyDiscard' superclass
-- (Fox's theorem): the comonoid supplied on every object is the natural one, @copy = id &&& id@
-- and @discard = terminate@.
testCartesian
  :: forall k
   . (Testable k, Cartesian.Cartesian k, TestOb (M.Unit @k))
  => (forall (a :: k) r. (TestOb a) => ((Ob a) => r) -> r)
  -> WithTestOb2 k
  -> TestTree
testCartesian withOb withTestOb2 = testProperty "Cartesian" $ do
  Some @a <- genOb @k
  withOb @a (withTestOb2 @a @a (propCartesianAt @a))

-- Hoisted so that @a ** a ~ a && a@ is an ordinary given ('Cartesian.TensorIsProduct'), which the
-- quantified superclass of 'Cartesian.Cartesian' can't supply as a rewrite on its own.
propCartesianAt
  :: forall {k} (a :: k)
   . ( Testable k
     , Cartesian.Cartesian k
     , Cartesian.TensorIsProduct a a
     , TestOb (M.Unit @k)
     , TestOb a
     , Ob a
     , TestOb (a M.** a)
     )
  => Property ()
propCartesianAt = do
  testEq "copy" "copy" (CopyDiscard.copy @k @a) "id &&& id" (BinaryProduct.diag @a)
  testEq "discard" "discard" (CopyDiscard.discard @k @a) "terminate" (Terminal.terminate @k @a)

testCartesian_ :: forall k. (Testable k, Cartesian.Cartesian k, TestObIsOb k, TestOb (M.Unit @k)) => TestTree
testCartesian_ =
  testCartesian @k (\ @a r -> obFromTestOb @a r) (\ @a @b r -> obFromTestOb @a (obFromTestOb @b (M.withOb2 @k @a @b r)))

-- | The tensor distributes over coproducts and is absorbed by the initial object: 'Distributive.distL',
-- 'Distributive.distR', 'Distributive.absorbL' and 'Distributive.absorbR' are isomorphisms, with
-- the inverses 'Distributive.distLInv', 'Distributive.distRInv' and 'Initial.initiate'.
testDistributive
  :: forall k
   . (Testable k, Distributive.Distributive k, TestOb (Initial.InitialObject :: k))
  => WithTestOb2 k
  -> WithTestObCoprod k
  -> TestTree
testDistributive withTestOb2 withTestObCoprod = testProperty "Distributive" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  withTestObCoprod @b @c $
    withTestObCoprod @a @b $
      withTestOb2 @a @b $
        withTestOb2 @a @c $
          withTestOb2 @b @c $
            withTestOb2 @a @(b BinaryCoproduct.|| c) $
              withTestOb2 @(a BinaryCoproduct.|| b) @c $
                withTestObCoprod @(a M.** b) @(a M.** c) $
                  withTestObCoprod @(a M.** c) @(b M.** c) $
                    withTestOb2 @a @(Initial.InitialObject :: k) $
                      withTestOb2 @(Initial.InitialObject :: k) @a $
                        do
                          propIso (Distributive.distL @k @a @b @c) (Distributive.distLInv @a @b @c)
                          propIso (Distributive.distR @k @a @b @c) (Distributive.distRInv @a @b @c)
                          propIso (Distributive.absorbL @k @a) Initial.initiate
                          propIso (Distributive.absorbR @k @a) Initial.initiate

testDistributive_ :: forall k. (Testable k, Distributive.Distributive k, TestObIsOb k) => TestTree
testDistributive_ =
  testDistributive @k
    (\ @a @b r -> M.withOb2 @k @a @b r)
    (\ @a @b r -> BinaryCoproduct.withObCoprod @k @a @b r)

-- | The laws of a closed monoidal category: the internal hom is a profunctor in its two arguments,
-- and 'Exponential.curry' and 'Exponential.uncurry' form a natural isomorphism.
testClosed
  :: forall k
   . (Testable k, Exponential.Closed k, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> WithTestObExp k
  -> TestTree
testClosed withTestOb2 withTestObExp =
  testGroup
    "Closed"
    [ testProperty "Exponential is functorial" $ do
        propProfunctorWith @(Rep (Exponential.ExpRep @k))
          ( do
              (Some @a, Some @b1, Some @b2) <-
                genWith
                  (Just . show)
                  ( genSuchThat ((,,) <$> genSomeSmall @k <*> genSomeSmall @k <*> genSomeSmall @k) \(Some @a, Some @b1, Some @b2) ->
                      withTestObExp @b1 @b2 (isGenNonEmpty @(Rep (Exponential.ExpRep @k) a '(OP b1, b2)))
                  )
              p <- withTestObExp @b1 @b2 (genNamed @(Rep (Exponential.ExpRep @k) a '(OP b1, b2)) "p")
              pure $ SomeP @a @'(OP b1, b2) p
          )
          (\ @_ @'(OP b1, b2) r -> withTestObExp @b1 @b2 r)
    , testProperty "Curry/uncurry is a natural isomorphism" $ do
        Some @a <- genObSmall @k
        Some @b <- genObSmall
        Some @c <- genObSmall
        withTestOb2 @a @b $ withTestObExp @b @c $ do
          propIsoP
            (Exponential.curry @k @a @b @c)
            (Exponential.uncurry @b @c)
          Some @a' <- genObSmall @k
          Some @b' <- genObSmall
          Some @c' <- genObSmall
          f <- genNamed @(a' ~> a) "f"
          g <- genNamed @(b' ~> b) "g"
          h <- genNamed @(c ~> c') "h"
          withTestOb2 @a' @b' $ withTestObExp @b' @c' $ do
            let n = dimap (f M.** g) h
            let n' = dimap f (h Exponential.^^^ g)
            testEq
              "natural curry"
              "curry . n"
              (Exponential.curry @k @a' @b' @c' . n)
              "n' . curry"
              (n' . Exponential.curry @k @a @b @c)
            testEq
              "natural uncurry"
              "uncurry . n'"
              (Exponential.uncurry @b' @c' . n')
              "n . uncurry"
              (n . Exponential.uncurry @b @c)
    ]

testClosed_ :: forall k. (Testable k, Exponential.Closed k, TestObIsOb k) => TestTree
testClosed_ =
  testClosed @k
    (\ @a @b r -> M.withOb2 @k @a @b r)
    (\ @a @b r -> Exponential.withObExp @k @a @b r)

-- | Laws of a *-autonomous category, in two halves that need disjoint objecthood.
--
-- 'SA.dual' being a contravariant functor, its hom-set bijection with 'SA.dualInv', and
-- 'SA.doubleNegIso' involve no tensor at all, so they need only the @withTestObDual@ witnesses.
-- The 'SA.linDist'\/'SA.linDistInv' bijection @Hom(a ** b, Dual c) ≅ Hom(a, Dual (b ** c))@ and
-- its naturality in all three variables need the tensor ones as well.
testStarAutonomous
  :: forall k
   . (Testable k, SA.StarAutonomous k, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> WithTestObDual k
  -> TestTree
testStarAutonomous withTestOb2 withTestObDual =
  testGroup
    "*-autonomous"
    [ testProperty "dual" $ do
        Some @a <- genOb @k
        Some @b <- genOb
        Some @c <- genOb
        withTestObDual @a $
          withTestObDual @(SA.Dual a) $
            withTestObDual @b $
              withTestObDual @c $ do
                f <- genNamed @(a ~> b) "f"
                g <- genNamed @(b ~> c) "g"
                g' <- genNamed @(SA.Dual b ~> SA.Dual a) "g"

                propIso' (SA.doubleNegIso @a)

                -- dual is a contravariant functor
                testEq "dual id" "dual id" (SA.dual @k @a @a (id @_ @a)) "id" id
                testEq
                  "dual composition"
                  "dual (g . f)"
                  (SA.dual @k @a @c (g . f))
                  "dual f . dual g"
                  (SA.dual @k @a @b f . SA.dual @k @b @c g)

                -- dual / dualInv establish a bijection on hom-sets
                testEq
                  "dualInv (dual f)"
                  "dualInv (dual f)"
                  (SA.dualInv @k @b @a (SA.dual @k @a @b f))
                  "f"
                  f
                testEq
                  "dual (dualInv g)"
                  "dual (dualInv g)"
                  (SA.dual @k @a @b (SA.dualInv @k @b @a g'))
                  "g"
                  g'
    , testProperty "linear distribution" $ do
        Some @a <- genOb @k
        Some @b <- genOb
        Some @c <- genOb
        Some @a' <- genOb @k
        Some @b' <- genOb @k
        Some @c' <- genOb @k
        withTestObDual @c $
          withTestObDual @c' $
            withTestOb2 @a @b $
              withTestOb2 @b @c $
                withTestOb2 @a' @b $
                  withTestOb2 @a @b' $
                    withTestOb2 @b' @c $
                      withTestOb2 @b @c' $
                        withTestObDual @(b M.** c) $
                          withTestObDual @(b' M.** c) $
                            withTestObDual @(b M.** c') $ do
                              p <- genNamed @(a M.** b ~> SA.Dual c) "p"
                              q <- genNamed @(a ~> SA.Dual (b M.** c)) "q"
                              fa <- genNamed @(a' ~> a) "f"
                              gb <- genNamed @(b' ~> b) "g"
                              hc <- genNamed @(c ~> c') "h"
                              p2 <- genNamed @(a M.** b ~> SA.Dual c') "p"

                              -- linDist / linDistInv establish a bijection Hom(a**b, Dual c) ≅ Hom(a, Dual (b**c))
                              testEq
                                "linDistInv (linDist p)"
                                "linDistInv (linDist p)"
                                (SA.linDistInv @k @a @b @c (SA.linDist @k @a @b @c p))
                                "p"
                                p
                              testEq
                                "linDist (linDistInv q)"
                                "linDist (linDistInv q)"
                                (SA.linDist @k @a @b @c (SA.linDistInv @k @a @b @c q))
                                "q"
                                q

                              -- naturality of linDist in a
                              testEq
                                "linDist naturality (a)"
                                "linDist p . f"
                                (SA.linDist @k @a @b @c p . fa)
                                "linDist (p . (f ** id))"
                                (SA.linDist @k @a' @b @c (p . (fa M.** obj @b)))

                              -- naturality of linDist in b
                              testEq
                                "linDist naturality (b)"
                                "dual (g ** id) . linDist p"
                                (SA.dual @k @(b' M.** c) @(b M.** c) (gb M.** obj @c) . SA.linDist @k @a @b @c p)
                                "linDist (p . (id ** g))"
                                (SA.linDist @k @a @b' @c (p . (obj @a M.** gb)))

                              -- naturality of linDist in c
                              testEq
                                "linDist naturality (c)"
                                "linDist (dual h . p)"
                                (SA.linDist @k @a @b @c (SA.dual @k @c @c' hc . p2))
                                "dual (id ** h) . linDist p"
                                (SA.dual @k @(b M.** c) @(b M.** c') (obj @b M.** hc) . SA.linDist @k @a @b @c' p2)
    ]

testStarAutonomous_ :: forall k. (Testable k, SA.StarAutonomous k, TestObIsOb k) => TestTree
testStarAutonomous_ =
  testStarAutonomous
    (\ @a @b r -> M.withOb2 @k @a @b r)
    (\ @a r -> r \\ SA.dualObj @a)

-- | Laws of a compact closed category: 'CC.distribDual'\/'CC.combineDual' establish an
-- isomorphism @Dual (a ** b) ≅ Dual a ** Dual b@ and 'CC.dualUnit'\/'CC.dualUnitInv' establish
-- @Dual Unit ≅ Unit@ (i.e. 'SA.Dual' is a strong monoidal functor); and the yanking\/zigzag
-- identities witness that @a@ and @Dual a@ are dual to one another via
-- 'CC.dualityUnit'\/'CC.dualityCounit'.
testCompactClosed
  :: forall k
   . (Testable k, CC.CompactClosed k, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> WithTestObDual k
  -> TestTree
testCompactClosed withTestOb2 withTestObDual = testProperty "Compact closed" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  withTestObDual @a $
    withTestObDual @b $
      withTestObDual @(M.Unit @k) $
        withTestOb2 @a @b $
          withTestOb2 @(SA.Dual a) @(SA.Dual b) $
            withTestOb2 @a @(SA.Dual a) $
              withTestOb2 @(SA.Dual a) @a $
                withTestOb2 @a @M.Unit $
                  withTestOb2 @M.Unit @a $
                    withTestOb2 @(SA.Dual a) @M.Unit $
                      withTestOb2 @M.Unit @(SA.Dual a) $
                        withTestObDual @(a M.** b) $
                          withTestOb2 @(a M.** SA.Dual a) @a $
                            withTestOb2 @a @(SA.Dual a M.** a) $
                              withTestOb2 @(SA.Dual a M.** a) @(SA.Dual a) $
                                withTestOb2 @(SA.Dual a) @(a M.** SA.Dual a) $ do
                                  -- distribDual / combineDual establish an isomorphism Dual (a**b) ≅ Dual a ** Dual b
                                  testEq
                                    "combineDual . distribDual"
                                    "combineDual (distribDual p)"
                                    (CC.combineDual @a @b . CC.distribDual @k @a @b)
                                    "id"
                                    id
                                  testEq
                                    "distribDual . combineDual"
                                    "distribDual (combineDual p)"
                                    (CC.distribDual @k @a @b . CC.combineDual @a @b)
                                    "id"
                                    id

                                  -- dualUnit / dualUnitInv establish an isomorphism Dual Unit ≅ Unit
                                  testEq
                                    "dualUnit . dualUnitInv"
                                    "dualUnit . dualUnitInv"
                                    (CC.dualUnit @k . CC.dualUnitInv)
                                    "id"
                                    id
                                  testEq
                                    "dualUnitInv . dualUnit"
                                    "dualUnitInv . dualUnit"
                                    (CC.dualUnitInv . CC.dualUnit @k)
                                    "id"
                                    id

                                  -- yanking / zigzag identity for a
                                  testEq
                                    "zigzag (a)"
                                    "rightUnitor . (id ** dualityCounit) . assoc . (dualityUnit ** id) . leftUnitorInv"
                                    ( M.rightUnitor @k @a
                                        . (obj @a M.** CC.dualityCounit @a)
                                        . M.associator @k @a @(SA.Dual a) @a
                                        . (CC.dualityUnit @a M.** obj @a)
                                        . M.leftUnitorInv @k @a
                                    )
                                    "id"
                                    id

                                  -- yanking / zigzag identity for Dual a
                                  testEq
                                    "zigzag (Dual a)"
                                    "leftUnitor . (dualityCounit ** id) . assocInv . (id ** dualityUnit) . rightUnitorInv"
                                    ( M.leftUnitor @k @(SA.Dual a)
                                        . (CC.dualityCounit @a M.** obj @(SA.Dual a))
                                        . M.associatorInv @k @(SA.Dual a) @a @(SA.Dual a)
                                        . (obj @(SA.Dual a) M.** CC.dualityUnit @a)
                                        . M.rightUnitorInv @k @(SA.Dual a)
                                    )
                                    "id"
                                    id

testCompactClosed_ :: forall k. (Testable k, CC.CompactClosed k, TestObIsOb k) => TestTree
testCompactClosed_ =
  testCompactClosed
    (\ @a @b r -> M.withOb2 @k @a @b r)
    (\ @a r -> r \\ SA.dualObj @a)

-- | Check 'propFrobenius' at randomly sampled objects.
testHypergraph
  :: forall k
   . (Testable k, M.SymMonoidal k, TestOb (M.Unit @k))
  => (forall (a :: k) r. (TestOb a) => ((Ob a, Hypergraph.Frobenius a) => r) -> r)
  -> WithTestOb2 k
  -> TestTree
testHypergraph withFrob withTestOb2 = testProperty "Hypergraph (Frobenius supply)" $ do
  Some @a <- genOb @k
  withFrob @a (propFrobenius @a (\ @x @y r -> withTestOb2 @x @y r))

testHypergraph_
  :: forall k
   . (Testable k, M.SymMonoidal k, TestObIsOb k, forall (a :: k). (TestOb a) => Hypergraph.Frobenius a)
  => TestTree
testHypergraph_ = testHypergraph @k (\r -> r) (\ @a @b r -> M.withOb2 @k @a @b r)

-- * Monoids and comonoids

-- | The monoid laws of @m@: 'Monoid.mempty' is a left and right unit for 'Monoid.mappend' (up to the
-- unitors), and 'Monoid.mappend' is associative (up to the associator).
propMonoid
  :: forall {k} m
   . (Testable k, Monoid.Monoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> Property ()
propMonoid withTestOb2 =
  withTestOb2 @M.Unit @m $
    withTestOb2 @m @M.Unit $ do
      testEq
        "left identity"
        "μ . (η ⊗ 1)"
        (Monoid.mappend . (Monoid.mempty @m M.** obj @m))
        "λ"
        (M.leftUnitor @k @m)
      testEq
        "right identity"
        "μ . (1 ⊗ η)"
        (Monoid.mappend . (obj @m M.** Monoid.mempty @m))
        "ρ"
        (M.rightUnitor @k @m)
      withTestOb2 @m @m $ withTestOb2 @(m M.** m) @m $ do
        testEq
          "associativity"
          "μ . (μ ⊗ 1)"
          (Monoid.mappend @m . (Monoid.mappend @m M.** obj @m))
          "μ . (1 ⊗ μ) . α"
          (Monoid.mappend . (obj @m M.** Monoid.mappend @m) . M.associator @k @m @m @m)

-- | The laws of a commutative monoid: 'propMonoid', and 'Monoid.mappend' is unchanged by 'M.swap'.
propCommutativeMonoid
  :: forall {k} m
   . (Testable k, Monoid.CommutativeMonoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> Property ()
propCommutativeMonoid withTestOb2 = do
  propMonoid @m (\ @x @y r -> withTestOb2 @x @y r)
  withTestOb2 @m @m $
    testEq
      "commutativity"
      "mappend . swap"
      (Monoid.mappend @m . M.swap @k @m @m)
      "mappend"
      (Monoid.mappend @m)

-- | The laws of a cocommutative comonoid, as those of a commutative monoid in the opposite category.
propCocommutativeComonoid
  :: forall {k} m
   . (Testable k, Monoid.CocommutativeComonoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> Property ()
propCocommutativeComonoid withTestOb2 = do
  propCommutativeMonoid @(OP m) (\ @(OP x) @(OP y) r -> withTestOb2 @x @y r)

-- | Check that the object @m@ is a special commutative 'Hypergraph.Frobenius' algebra: it is a
-- 'Monoid.CommutativeMonoid' (via 'propCommutativeMonoid') and a 'Monoid.CocommutativeComonoid'
-- (via 'propCocommutativeComonoid'), and satisfies speciality (@mappend . comult = id@) and the
-- Frobenius condition. A 'Hypergraph.Hypergraph' category supplies this structure, and
-- @'testHypergraph'@ samples an object and delegates here.
propFrobenius
  :: forall {k} m
   . ( Testable k
     , M.SymMonoidal k
     , Monoid.CommutativeMonoid (m :: k)
     , Monoid.CocommutativeComonoid m
     , TestOb m
     , TestOb (M.Unit @k)
     )
  => WithTestOb2 k
  -> Property ()
propFrobenius withTestOb2 = do
  propCommutativeMonoid @m (\ @x @y r -> withTestOb2 @x @y r)
  propCocommutativeComonoid @m (\ @x @y r -> withTestOb2 @x @y r)
  withTestOb2 @m @m $
    withTestOb2 @(m M.** m) @m $ do
      let mu = Monoid.mappend @m
          delta = Monoid.comult @m
      testEq
        "speciality"
        "mappend . comult"
        (mu . delta)
        "id"
        (obj @m)
      testEq
        "Frobenius condition (left)"
        "(mappend ** id) . associatorInv . (id ** comult)"
        ((mu M.** obj @m) . M.associatorInv @k @m @m @m . (obj @m M.** delta))
        "comult . mappend"
        (delta . mu)
      testEq
        "Frobenius condition (right)"
        "(id ** mappend) . associator . (comult ** id)"
        ((obj @m M.** mu) . M.associator @k @m @m @m . (delta M.** obj @m))
        "comult . mappend"
        (delta . mu)

-- | The monoid laws of @m@ ('propMonoid') as a ready-made test.
testMonoid
  :: forall {k} m
   . (Testable k, Monoid.Monoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> TestTree
testMonoid f = testProperty ("Monoid " ++ showOb @k @m) (propMonoid @m \ @a @b -> f @a @b)

testMonoid_ :: forall {k} m. (Testable k, Monoid.Monoid (m :: k), TestObIsOb k) => TestTree
testMonoid_ = testMonoid @m (\ @a @b r -> M.withOb2 @k @a @b r)

-- | The comonoid laws of @m@, as the monoid laws of @m@ in the opposite category.
testComonoid
  :: forall {k} m
   . (Testable k, Monoid.Comonoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> TestTree
testComonoid f = testProperty ("Comonoid " ++ showOb @k @m) (propMonoid @(OP m) \ @(OP a) @(OP b) r -> f @a @b r)

testComonoid_ :: forall {k} m. (Testable k, Monoid.Comonoid (m :: k), TestObIsOb k) => TestTree
testComonoid_ = testComonoid @m (\ @a @b r -> M.withOb2 @k @a @b r)

-- | The laws of a commutative monoid ('propCommutativeMonoid') as a ready-made test.
testCommutativeMonoid
  :: forall {k} m
   . (Testable k, Monoid.CommutativeMonoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> TestTree
testCommutativeMonoid f = testProperty ("CommutativeMonoid " ++ showOb @k @m) (propCommutativeMonoid @m \ @a @b -> f @a @b)

testCommutativeMonoid_ :: forall {k} m. (Testable k, Monoid.CommutativeMonoid (m :: k), TestObIsOb k) => TestTree
testCommutativeMonoid_ = testCommutativeMonoid @m (\ @a @b r -> M.withOb2 @k @a @b r)

-- | The laws of a cocommutative comonoid ('propCocommutativeComonoid') as a ready-made test.
testCocommutativeComonoid
  :: forall {k} m
   . (Testable k, Monoid.CocommutativeComonoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => WithTestOb2 k
  -> TestTree
testCocommutativeComonoid f = testProperty ("CocommutativeComonoid " ++ showOb @k @m) (propCocommutativeComonoid @m \ @a @b -> f @a @b)

testCocommutativeComonoid_
  :: forall {k} m
   . (Testable k, Monoid.CocommutativeComonoid (m :: k), TestObIsOb k)
  => TestTree
testCocommutativeComonoid_ = testCocommutativeComonoid @m (\ @a @b r -> M.withOb2 @k @a @b r)

-- | The laws of a special commutative Frobenius algebra ('propFrobenius') as a ready-made test.
testFrobenius
  :: forall {k} (m :: k)
   . ( Testable k
     , Monoid.CommutativeMonoid m
     , Monoid.CocommutativeComonoid m
     , TestOb m
     , TestOb (M.Unit @k)
     )
  => WithTestOb2 k
  -> TestTree
testFrobenius f = testProperty ("Frobenius " ++ showOb @k @m) (propFrobenius @m \ @a @b -> f @a @b)

testFrobenius_
  :: forall {k} (m :: k)
   . ( Testable k
     , Monoid.CommutativeMonoid m
     , Monoid.CocommutativeComonoid m
     , TestObIsOb k
     )
  => TestTree
testFrobenius_ = testFrobenius @m (\ @a @b r -> M.withOb2 @k @a @b r)

-- * Toposes

-- | Checks the subobject classifier @'Topos.Omega'@, the object of truth values: a map into it is a
-- predicate, and each mono @m@ has one classifying map, 'Topos.true' on @m@ and nowhere else. The
-- laws quantify over generalized elements (arrows into the object):
--
-- * @'Topos.classifyGraph' f@ is 'Topos.true' at @(x, y)@ iff @y = f . x@. This is the pullback
--   condition for the graph @\<id, f\>@. At @f = 'id'@ it is 'Topos.isEq', so equality testing is
--   pinned down too.
-- * Distinct arrows get distinct classifiers, the testable consequence of the classifying map
--   being unique.
-- * @'Topos.classifyKernelPair' f@ is true at @(x, x\')@ iff @f@ identifies them, in both directions.
-- * @'Topos.classifyImage' f@ is true on the image of @f@ and nowhere else: every element it calls
--   true factors through the image mono, by 'Pullback.factorPullback'. This is the law that
--   separates a subobject classifier from an arbitrary map into 'Topos.Omega'.
--
-- The elements come from the 'Testable' palette, which is sound iff that palette generates: true
-- for the concrete finite categories, not for a presheaf topos.
testSubobjectClassifier
  :: forall k
   . ( Testable k
     , Topos.HasSubobjectClassifier k
     , Topos.HasEpiMonoFactorization k
     , Pushout.HasPushouts k
     , Pullback.HasPullbacks k
     , TestOb (Topos.Omega :: k)
     )
  => WithTestObProd k
  -> TestTree
testSubobjectClassifier withTestObProd = testProperty "Subobject classifier" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @z <- genOb
  f <- genNamed @(a ~> b) "f"
  x <- genNamed @(z ~> a) "x"
  y <- genNamed @(z ~> b) "y"
  inGraph <- eqP (f . x) y
  classified <-
    eqP (Topos.classifyGraph f . (x BinaryProduct.&&& y)) (Terminal.const Topos.true)
  expect "classifyGraph is true exactly on the graph of f" inGraph classified
  g <- genNamed @(a ~> b) "g"
  withTestObProd @a @b @(Property ()) $ do
    eqChi <- eqP (Topos.classifyGraph f) (Topos.classifyGraph g)
    propReflectsEq "classifier injective" "classifyGraph f == classifyGraph g" eqChi f g
  x' <- genNamed @(z ~> a) "x'"
  identified <- eqP (f . x) (f . x')
  kernelPair <-
    eqP (Topos.classifyKernelPair f . (x BinaryProduct.&&& x')) (Terminal.const Topos.true)
  expect "classifyKernelPair is true exactly when f identifies the pair" identified kernelPair
  -- bound once: in the sheaves this is a pushout, which sheafifies and tabulates its apex
  let chi = Topos.classifyImage f
  onImage <- eqP (chi . (f . x)) (Terminal.const Topos.true)
  expect "classifyImage f is true on the image of f" True onImage
  -- The converse, which makes this a /subobject/ classifier: anything the classifier calls true
  -- factors through the image mono. Mirrors the existence half of 'testEqualizers'.
  case Topos.factorize f of
    (:.:) _ m@Objs -> do
      w <- genNamed @(z ~> b) "w"
      classifiedTrue <- eqP (chi . w) (Terminal.const Topos.true)
      when classifiedTrue $
        testEq
          "image factorization"
          "m . factorPullback m terminate w terminate"
          (m . Pullback.factorPullback m Terminal.terminate w Terminal.terminate)
          "w"
          w

testSubobjectClassifier_
  :: forall k
   . ( Testable k
     , Topos.HasSubobjectClassifier k
     , Topos.HasEpiMonoFactorization k
     , Pushout.HasPushouts k
     , Pullback.HasPullbacks k
     , TestObIsOb k
     , TestOb (Topos.Omega :: k)
     )
  => TestTree
testSubobjectClassifier_ =
  testSubobjectClassifier @k (\ @a @b r -> BinaryProduct.withObProd @k @a @b r)

-- | Negation is implication into false:
-- @'Topos.not' = 'Topos.implies' . (id '&&&' 'Terminal.const' 'Topos.false')@. A theorem of
-- every topos; 'Topos.not' is defined as the classifying map of 'Topos.false' instead, so this
-- checks the two agree.
testNegation :: forall k. (Testable k, Topos.ElementaryTopos k, TestOb (Topos.Omega :: k)) => TestTree
testNegation =
  testProperty "negation is implication into false" $
    testEq
      "not"
      "not"
      (Topos.not @k)
      "implies . (id &&& const false)"
      (Topos.implies . (id BinaryProduct.&&& Terminal.const Topos.false))

-- | The three equations a Lawvere–Tierney topology satisfies, for an arrow
-- @j :: 'Topos.Omega' '~>' 'Topos.Omega'@: it fixes @true@, is idempotent, and preserves meets.
--
-- Such a @j@ is the same data as a Grothendieck topology: the covering sieves are the ones @j@
-- sends to @true@. 'FinSheaf.lawvereTierney' is the @j@ a coverage induces, so this is how a
-- coverage's stability and composition get checked, without quantifying over arrows the coverage
-- was never handed.
testLawvereTierney
  :: forall k
   . (Testable k, Topos.ElementaryTopos k, TestOb (Topos.Omega :: k), TestOb (Terminal.TerminalObject :: k))
  => WithTestObProd k
  -> (Topos.Omega :: k) ~> Topos.Omega
  -> TestTree
testLawvereTierney withTestObProd j =
  testGroup
    "Lawvere-Tierney topology"
    [testProperty name (law j) | (name, law) <- lawvereTierneyLaws @k (\ @a @b r -> withTestObProd @a @b r)]

-- | The three laws of 'testLawvereTierney', by name, for an arrow given later. Shared by it and
-- 'testLawvereTierneyFamily'.
lawvereTierneyLaws
  :: forall k
   . (Testable k, Topos.ElementaryTopos k, TestOb (Topos.Omega :: k), TestOb (Terminal.TerminalObject :: k))
  => WithTestObProd k
  -> [(String, (Topos.Omega :: k) ~> Topos.Omega -> Property ())]
lawvereTierneyLaws withTestObProd =
  [ ("fixes true", \j -> testEq "true" "j . true" (j . Topos.true) "true" Topos.true)
  , ("idempotent", \j -> testEq "idempotent" "j . j" (j . j) "j" j)
  ,
    ( "preserves meets"
    , \j ->
        withTestObProd @Topos.Omega @Topos.Omega @(Property ()) $
          testEq "meets" "j . and" (j . Topos.and) "and . (j *** j)" (Topos.and . (j BinaryProduct.*** j))
    )
  ]

-- | 'testLawvereTierney' for a family of arrows indexed by the truth values, at a generated one:
-- 'Topos.openTopology' and 'Topos.closedTopology' are the ones the internal logic gives.
testLawvereTierneyFamily
  :: forall k
   . (Testable k, Topos.ElementaryTopos k, TestOb (Topos.Omega :: k), TestOb (Terminal.TerminalObject :: k))
  => String
  -> WithTestObProd k
  -> ((Terminal.TerminalObject :: k) ~> Topos.Omega -> (Topos.Omega :: k) ~> Topos.Omega)
  -> TestTree
testLawvereTierneyFamily name withTestObProd family =
  testGroup
    name
    [ testProperty lawName (genNamed "u" >>= law . family)
    | (lawName, law) <- lawvereTierneyLaws @k (\ @a @b r -> withTestObProd @a @b r)
    ]

testLawvereTierney_
  :: forall k
   . ( Testable k
     , Topos.ElementaryTopos k
     , TestObIsOb k
     , TestOb (Topos.Omega :: k)
     , TestOb (Terminal.TerminalObject :: k)
     )
  => (Topos.Omega :: k) ~> Topos.Omega
  -> TestTree
testLawvereTierney_ =
  testLawvereTierney @k (\ @a @b r -> obFromTestOb @a (obFromTestOb @b (BinaryProduct.withObProd @k @a @b r)))

testLawvereTierneyFamily_
  :: forall k
   . ( Testable k
     , Topos.ElementaryTopos k
     , TestObIsOb k
     , TestOb (Topos.Omega :: k)
     , TestOb (Terminal.TerminalObject :: k)
     )
  => String
  -> ((Terminal.TerminalObject :: k) ~> Topos.Omega -> (Topos.Omega :: k) ~> Topos.Omega)
  -> TestTree
testLawvereTierneyFamily_ name =
  testLawvereTierneyFamily @k name (\ @a @b r -> obFromTestOb @a (obFromTestOb @b (BinaryProduct.withObProd @k @a @b r)))

-- * Sites and sheaves

-- | The three laws a listable, stable coverage owes, as one group: 'testStableSite',
-- 'testGeneratedSieveIsSieve' and 'testDenseIsCovering'. Checking a site starts here.
--
-- The rest of this section checks what is built on the coverage: 'testGluesBack' and
-- 'testGluesBackAt' the sheaf condition, 'testEqualizersAreSheaves' the category of sheaves, and
-- 'testSheafification' (with 'testPlusFixes') the reflector. 'testLawvereTierney', under Toposes,
-- checks the generated topology and with it 'Sheaf.HasFiniteCovers'\'s Composition law.
testSiteLaws
  :: forall t j k
   . (Sheaf.StableSite t k, Sheaf.HasFiniteCovers t k, Finitary.FiniteCat j, Finitary.FiniteCat k)
  => TestTree
testSiteLaws =
  testGroup
    "site laws"
    [testStableSite @t @k, testGeneratedSieveIsSieve @t @j @k, testDenseIsCovering @t @j @k]

-- | 'Sheaf.StableSite'\'s law: pulling a cover back along @f@ gives a cover. For every leg @l'@ of
-- the cover 'Sheaf.pullbackCover' returns, the instance names a leg @l@ of the original and a
-- factor @u@ with @f '.' 'Sheaf.legArrow' l' = 'Sheaf.legArrow' l '.' u@. This checks that
-- equation, and that the pulled-back legs generate a covering sieve, which matters for covers that
-- are built instead of listed, like the meets of 'Proarrow.Category.Sheaf.Joins'. Covering is
-- checked instead of dense so that the check does not assume covers compose. It runs at
-- @j ~ ()@, since whether a sieve covers does not depend on @j@.
--
-- On a thin site (at most one arrow between two objects) the equation holds as soon as it
-- typechecks. It bites only where two legs share a source and target: the ends of an edge in the
-- graph schema @E ⇉ V@, or 'Proarrow.Category.Sheaf.ByElements', whose legs are named by elements.
testStableSite
  :: forall t k. (Sheaf.StableSite t k, Sheaf.HasFiniteCovers t k, Finitary.FiniteCat k) => TestTree
testStableSite =
  testProperty "covers pull back" $
    sequence_
      ( Finitary.foreachOb @k @(Property ()) \ @a -> Finitary.foreachOb @k @(Property ()) \ @b ->
          [ case Sheaf.pullbackCover c f of
              -- the arrow itself factors, so the pullback is @b@\'s implicit identity cover
              Sheaf.AlreadyFactors fs -> propFactorsThroughLeg @t f fs
              Sheaf.PulledBack c' fs -> do
                expect
                  ("the pulled-back cover of object " ++ show (Finitary.objIndex @b) ++ " covers it")
                  True
                  (FinSheaf.isCovering @t (FinSheaf.generatedSieve @t @b @'() c'))
                sequence_ [propFactorsThroughLeg @t (f . Sheaf.legArrow l) (fs l) | Sheaf.SomeLeg l <- Sheaf.legs c']
          | Sheaf.SomeCover c <- Sheaf.covers @t @k @a
          , f <- Finitary.elements @(Hom k) @b @a
          ]
      )

-- | One leg\'s half of 'testStableSite': the arrow is the leg it factors through, composed with
-- the factor.
propFactorsThroughLeg
  :: forall t {k} (a :: k) c x
   . (Sheaf.Site t k, Finitary.FiniteCat k, Ob a)
  => x ~> a
  -> Sheaf.Factors t k a c x
  -> Property ()
propFactorsThroughLeg f (Sheaf.Factors l u) =
  -- the factor is what brings its own source into scope, and the result type is known here, where
  -- at the call site it would be under an untouchable variable
  u //
    expect
      "the arrow factors through the leg the pullback names"
      (Finitary.toIndex @(Hom k) @x @a f)
      (Finitary.toIndex (Sheaf.legArrow l . u))

-- | A cover's generated sieve (the arrows that factor through one of its legs) is a sieve: closed
-- under composing on either side, as 'FinTopos.closedUnder' decides. That holds for any coverage,
-- lawful or not, so this checks 'Finitary.factorsThrough' and the hom-profunctor's
-- 'Finitary.elements', which every verdict in "Proarrow.Category.Enriched.Finitary.Sheaf" is read
-- off. It catches, for instance, an argument-swapped 'Finitary.factorsThrough'.
testGeneratedSieveIsSieve
  :: forall t j k. (Sheaf.HasFiniteCovers t k, Finitary.FiniteCat j, Finitary.FiniteCat k) => TestTree
testGeneratedSieveIsSieve =
  testProperty "generated sieves are sieves" $
    sequence_
      ( Finitary.foreachOb @k @(Property ()) \ @a -> Finitary.foreachOb @j @(Property ()) \ @b ->
          [ case FinSheaf.generatedSieve @t @a @b c of
              Sieve inSieve ->
                expect
                  ("the sieve a cover of object " ++ show (Finitary.objIndex @a) ++ " generates")
                  True
                  (FinTopos.closedUnder @(Yo a (OP b)) \(Yo g h) -> inSieve g h)
          | Sheaf.SomeCover c <- Sheaf.covers @t @k @a
          ]
      )

-- | On a category with pullbacks (which give the Ore condition), the topology 'Sheaf.Atomic'
-- generates is the double-negation one: 'FinSheaf.lawvereTierney' and 'Topos.doubleNegation' are
-- the same arrow, one computed by closing sieves and one from the internal logic. At @j ~ ()@
-- only: over a non-trivial @j@, @¬¬@ is the dense topology along @j@ as well, while the coverage
-- acts on @k@ alone.
testAtomicIsDoubleNegation
  :: forall k
   . ( Pullback.HasPullbacks k
     , Finitary.FiniteCat k
     , Testable (BinaryProduct.PROD (FinTopos.FINITARY () k))
     , TestOb (Topos.Omega :: BinaryProduct.PROD (FinTopos.FINITARY () k))
     )
  => TestTree
testAtomicIsDoubleNegation =
  testProperty "double negation is the atomic topology" $
    testEq
      "¬¬"
      "doubleNegation"
      (Topos.doubleNegation @(BinaryProduct.PROD (FinTopos.FINITARY () k)))
      "lawvereTierney @Atomic"
      (FinSheaf.lawvereTierney @Sheaf.Atomic)

-- | For every sieve at every pair of objects of a finite site: it is covering exactly when it is dense,
-- that is when its 'FinSheaf.closure' is the maximal sieve. Two independent computations of one
-- fact: 'FinSheaf.isCovering' reads it off the coverage, 'FinSheaf.closure' off the induced
-- topology.
testDenseIsCovering
  :: forall t j k. (Sheaf.HasFiniteCovers t k, Finitary.FiniteCat j, Finitary.FiniteCat k) => TestTree
testDenseIsCovering =
  testProperty "covering sieves are the dense ones" $
    sequence_
      ( Finitary.foreachOb @k @(Property ()) \ @a -> Finitary.foreachOb @j @(Property ()) \ @b ->
          [ expect
              ("sieve " ++ show (Finitary.toIndex s) ++ " at object " ++ show (Finitary.objIndex @a))
              (FinSheaf.isCovering @t s)
              (FinSheaf.isDense @t s)
          | s <- Finitary.elements @(Sieve :: j +-> k) @a @b
          ]
      )

-- | The uniqueness half of the sheaf condition at one cover: an element @x@ at the covered object
-- is the gluing of its own restrictions to the legs.
--
-- The other half (a glued element restricts back to the family) has no generic test: the only
-- matching family generic code can build is an element's own restrictions, and there it follows
-- from uniqueness. Other families come from the site, so that test is written per site. At a
-- finite site 'Proarrow.Category.Enriched.Finitary.Sheaf.isSheaf' decides both halves at once, by
-- checking that restriction is a bijection onto the matching families.
propGluesBack
  :: forall {j} {k} t (p :: j +-> k) (a :: k) (b :: j) c
   . (Sheaf.Sheaf t p, Ob a, Ob b, TestingEqShow (p a b))
  => Sheaf.Cover t k a c
  -> p a b
  -> Property ()
propGluesBack c x =
  testEq
    "uniqueness"
    "glue c (\\g -> lmap (legArrow g) x)"
    (Sheaf.glue @t c \g -> lmap (Sheaf.legArrow g) x)
    "x"
    x

-- | 'propGluesBack' at every cover of a random element's object. Named for the law and not for the
-- class, since it is half of what 'Sheaf.Sheaf' asks for (see 'propGluesBack' for the other half).
--
-- The object is drawn from those that actually have a cover: on a site where only some objects are
-- covered, drawing uniformly would leave most runs asserting nothing while reporting successes.
testGluesBack
  :: forall {j} {k} t (p :: j +-> k)
   . (Sheaf.HasFiniteCovers t k, Sheaf.Sheaf t p, TestableProfunctor p, TestableTypeP p, TestObIsOb k)
  => TestTree
testGluesBack = testProperty "glues back" do
  Some @a <- genObSuchThat @k \(Some @a) -> not (null (Sheaf.covers @t @k @a))
  Some @b <- genOb @j
  x <- genNamed @(p a b) "x"
  obFromTestOb @a $
    obFromTestOb @b $
      for_ (Sheaf.covers @t @k @a) \(Sheaf.SomeCover c) -> propGluesBack @t c x

-- | 'propGluesBack' at one named cover, for a site whose covers cannot be listed. The label names
-- the profunctor and cover, which nothing in the type can supply.
testGluesBackAt
  :: forall {j} {k} t (p :: j +-> k) (a :: k) c
   . (Sheaf.Sheaf t p, TestableProfunctor p, TestableTypeP p, TestOb a)
  => String
  -> Sheaf.Cover t k a c
  -> TestTree
testGluesBackAt lbl c = testProperty ("glues back at " ++ lbl) do
  Some @b <- genOb @j
  x <- genNamed @(p a b) "x"
  obFromTestOb @a $ obFromTestOb @b $ propGluesBack @t c x

-- | An equalizer of sheaves is a sheaf, for every coverage: the 'Sheaf.Sheaf' instance for
-- 'FinTopos.Reindex' presupposes that the table cuts out a /subsheaf/, and this decides it, by
-- 'FinSheaf.isSheaf', on the equalizer of every pair of parallel arrows the palette of
-- @'FinSheaf.SHEAVES' t j k@ can form.
testEqualizersAreSheaves
  :: forall t j k
   . (Testable (FinSheaf.SHEAVES t j k), Sheaf.HasFiniteCovers t k, Finitary.FiniteCat j, Finitary.FiniteCat k)
  => TestTree
testEqualizersAreSheaves = testProperty "equalizers are sheaves" do
  SomeP @a @b f <- genProfunctorElt @(Hom (FinSheaf.SHEAVES t j k)) "f"
  g <- genNamed @(a ~> b) "g"
  Equalizer.equalize f g \(Sub (Prof @e _)) -> expect "isSheaf of the equalizer" True (FinSheaf.isSheaf @t @e)

-- | Sheafification is the reflector into the sheaves: it turns a presheaf @p@ into the closest
-- sheaf, and every map from @p@ to a sheaf factors uniquely through it. For a finitary @p@ and a
-- sheaf @q@, decided at a finite site:
--
-- * @'FinSheaf.unitPlus'@ is natural;
-- * @'FinSheaf.Sheafify' t p@ is a sheaf, by 'FinSheaf.isSheaf';
-- * one plus construction fixes @q@ ('testPlusFixes');
-- * maps @'FinSheaf.Sheafify' t p ~> q@ correspond to maps @p ~> q@. The hom-sets of
--   @'FinTopos.FINITARY' j k@ are finite, so this is a count, made a bijection by
--   'FinSheaf.extendSheafify': extending every map @p ~> q@ gives every map out of the
--   sheafification once, and restricting an extension along the unit gives the map back.
--
-- This also makes 'FinSheaf.extendPlus'\'s choice of cover safe to leave unspecified: another
-- choice would show up here as an extension that is not one of the maps.
testSheafification
  :: forall t {j} {k} (p :: j +-> k) (q :: j +-> k)
   . ( Sheaf.HasFiniteCovers t k
     , Sheaf.Sheaf t q
     , Finitary.Finitary p
     , Finitary.Finitary q
     , Finitary.FiniteCat j
     , Finitary.FiniteCat k
     , Testable j
     , Testable k
     , TestableProfunctor p
     )
  => TestTree
testSheafification =
  testGroup
    "sheafification"
    [ testProperty "unit is natural" $ propNaturalTransformation @p @(FinSheaf.Plus t p) (FinSheaf.unitPlus @t)
    , testProperty "Sheafify p is a sheaf" $ expect "isSheaf" True (FinSheaf.isSheaf @t @(FinSheaf.Sheafify t p))
    , testPlusFixes @t @q
    , testProperty "left adjoint to inclusion" do
        -- both enumerations once: each is a full walk of the finitary hom-set
        let maps = FinTopos.natTransformations @p @q
            exts = FinTopos.natElements @(FinSheaf.Sheafify t p) @q
        -- a hom-set is empty whenever @q@ runs out of elements where @p@ has some, and then every
        -- assertion below holds of nothing
        expect "there are maps to extend" True (not (null maps))
        expect "as many maps out of the sheafification as out of p" (length maps) (length exts)
        expect
          "the extensions are exactly the maps out of the sheafification"
          (sort exts)
          (sort [FinTopos.natTable @(FinSheaf.Sheafify t p) @q (FinSheaf.extendSheafify @t n) | Prof n <- maps])
        for_ maps \(Prof n) ->
          expect
            "restricting an extension along the unit gives the map back"
            (FinTopos.natTable @p @q n)
            (FinTopos.natTable @p @q \x -> FinSheaf.extendSheafify @t n (FinSheaf.unitSheafify @t x))
    ]

-- | One plus leaves a sheaf as it was: 'FinSheaf.unitPlus' is a bijection at every pair of objects.
-- Stated for any finitary @q@ (the property needs no 'Sheaf.Sheaf' instance, only 'FinSheaf.isSheaf'
-- to be true of @q@), so it also serves at a coverage no profunctor has an instance for, such as the
-- trivial one, which fixes everything.
testPlusFixes
  :: forall t {j} {k} (q :: j +-> k)
   . (Sheaf.HasFiniteCovers t k, Finitary.Finitary q, Finitary.FiniteCat j, Finitary.FiniteCat k)
  => TestTree
testPlusFixes =
  testProperty "one plus fixes q" $
    sequence_
      ( Finitary.foreachOb @k @(Property ()) \ @a -> Finitary.foreachOb @j @(Property ()) \ @b ->
          -- bound once for the hom-set: at 'FinSheaf.Plus' one 'Finitary.toIndex' is an enumeration
          let ix = Finitary.toIndex @(FinSheaf.Plus t q) @a @b
          in [ expect
                 ("unit is a bijection at object " ++ show (Finitary.objIndex @a))
                 (Finitary.indices (Finitary.size @(FinSheaf.Plus t q) @a @b))
                 (sort [ix (FinSheaf.unitPlus @t x) | x <- Finitary.elements @q @a @b])
             ]
      )
