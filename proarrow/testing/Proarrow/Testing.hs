{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}

-- | Generic property-testing infrastructure for categories: 'Testable' says how to generate and
-- enumerate the objects of a kind, 'TestableProfunctor' and 'TestableType' how to generate values
-- (using @falsify@ generators), and 'TestingEqShow' provides semantic equality and display for
-- values without useful structural 'Eq'\/'Show' (functions, opaque morphisms). Instances for your
-- own category plus the law checks in "Proarrow.Testing.Laws" give it a test suite.
module Proarrow.Testing
  ( -- * Describing a category
    Testable (..)
  , TestableProfunctor (..)
  , TestableType (..)
  , TestableTypeP
  , TestingEqShow (..)
  , TestObIsOb
  , TestOb'
  , obFromTestOb

    -- * Objecthood witnesses
  , WithTestOb
  , WithTestOb2
  , WithTestObProd
  , WithTestObCoprod
  , WithTestObExp
  , WithTestObDual
  , WithTestObRep
  , WithTestObCorep

    -- * Objects
  , Some (..)
  , mapSome
  , genOb
  , genObSmall
  , genObSuchThat
  , genSomeDef
  , genSomeFinite
  , genSomeList
  , MkSomeList (..)

    -- * Profunctor elements
  , SomeProfunctorElt (..)
  , someP

    -- * Generators

    -- | @falsify@ generators, wrapped so that an empty type is a first-class case rather than a
    -- generator that fails at run time: match 'GenEmpty' first, then 'GenNonEmpty'. The two are a
    -- @COMPLETE@ set. The representation behind 'GenNonEmpty' is not exported on purpose. Go
    -- through the pattern, which is total.
  , GenTotal (GenEmpty)
  , pattern GenNonEmpty
  , invmap
  , isGenNonEmpty
  , optGen
  , oneElem
  , genBoth
  , genElements
  , oneOfTotal
  , genP
  , genNamed
  , genWithNamed
  , genSuchThat
  , someElem
  , someElemNamed
  , someElemWith

    -- * Generating functions

    -- | 'ShowP' supplies the 'Show' instance @falsify@ needs on both parameters of a generated
    -- 'Test.Falsify.Generator.Fun', derived from 'showP'; 'applyFunP' unwraps on the way back out.
  , ShowP (..)
  , applyFunP

    -- * Assertions
  , expect
  , testEq
  , eqHask

    -- * Interactive debugging

    -- | Run a generator once in @ghci@ and print what it produced. These trace to stdout and are
    -- for exploring a generator by hand, not for use inside a test.
  , sampleT
  , sampleP
  , sampleK
  ) where

import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (mapMaybe)
import GHC.Exts qualified as GHC
import Test.Falsify.Generator (Fun, Function (..), Gen, applyFun, elem, fun, functionMap, minimalValue, oneof)
import Test.Tasty.Falsify (Property, discard, genWith, testFailed)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Control.Applicative (Alternative (..))
import Control.Monad (ap, unless)
import Debug.Trace (traceM, traceShowM)
import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, foreachOb)
import Proarrow.Category.Enriched.Finitary.Sheaf (ClosedSieve (..), Plus, plusTable, samePlus)
import Proarrow.Category.Enriched.Finitary.Topos (KnownTables, Tabulated (..), natTable, natTransformations, sieveTable)
import Proarrow.Category.Enriched.Thin (Enumerable)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product (Fst, Snd, (:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed qualified as Exponential
import Proarrow.Category.Monoidal.StarAutonomous qualified as SA
import Proarrow.Category.Sheaf (HasFiniteCovers)
import Proarrow.Colimit.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Core (CAT, CategoryOf (..), Hom, Is, OB, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (type (@))
import Proarrow.Functor qualified as Rep
import Proarrow.Limit.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Limit.BinaryProduct qualified as BinaryProduct
import Proarrow.Object (Ob')
import Proarrow.Profunctor.Corepresentable (type (%%))
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Instance.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Instance.Product (fstP, sndP, (:*:) (..))
import Proarrow.Profunctor.Instance.Ran (Ran (..))
import Proarrow.Profunctor.Instance.Rift (Rift (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve)
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))
import Proarrow.Profunctor.Representable (Rep (..), type (%))
import Test.Falsify.Interactive (falsify)

data GenTotal a where
  GenEmpty :: ~(forall x. a -> x) -> GenTotal a
  GenNENonFun :: Gen a -> GenTotal a
  GenFun :: (TestableType a, TestableType b) => ((a -> b) -> p) -> Gen (Fun (ShowP a) (ShowP b)) -> GenTotal p

invmap :: (a -> b) -> (b -> a) -> GenTotal a -> GenTotal b
invmap _ f' (GenEmpty g) = GenEmpty (g . f')
invmap f _ (GenNENonFun g) = GenNENonFun (fmap f g)
invmap f _ (GenFun f' g) = GenFun (f . f') g

flatten :: GenTotal a -> Gen a
flatten (GenNENonFun g) = g
flatten (GenFun f g) = f . applyFunP <$> g
flatten (GenEmpty _) = error "flatten: Match on GenEmpty first"

pattern GenNonEmpty :: Gen a -> GenTotal a
pattern GenNonEmpty g <- (flatten -> g)
  where
    GenNonEmpty g = GenNENonFun g

{-# COMPLETE GenEmpty, GenNonEmpty #-}

instance Functor GenTotal where
  fmap f = invmap f (error "fmap GenTotal")

instance Applicative GenTotal where
  pure a = GenNENonFun (pure a)
  (<*>) = ap

instance Alternative GenTotal where
  empty = GenEmpty (error "empty")
  GenEmpty f <|> GenEmpty _ = GenEmpty f
  GenEmpty _ <|> g = g
  f <|> GenEmpty _ = f
  GenNonEmpty g <|> GenNonEmpty h = GenNonEmpty (oneof (g :| [h]))

-- | Uniformly choose among any number of alternatives, dropping the empty ones. Plain '<|>'
-- only combines two generators at 50\/50, so chaining it over more than two alternatives
-- associates pairwise and skews weight towards whichever branch ends up outermost in the
-- resulting tree. Use this whenever there are more than two alternatives to pick fairly among.
oneOfTotal :: [GenTotal a] -> GenTotal a
oneOfTotal gts = case mapMaybe toGen gts of
  [] -> empty
  g : gs -> GenNonEmpty (oneof (g :| gs))
  where
    toGen (GenEmpty _) = Nothing
    toGen (GenNonEmpty g) = Just g

instance Monad GenTotal where
  GenEmpty _ >>= _ = GenEmpty (error ">>= GenEmpty")
  GenNonEmpty g >>= f = case f (minimalValue g) of
    GenEmpty x -> GenEmpty x
    _ -> GenNonEmpty do
      p <- fmap f g
      case p of
        GenEmpty _ -> error ">>= GenEmpty"
        GenNonEmpty g' -> g'

class TestingEqShow a where
  eqP :: a -> a -> Property Bool
  default eqP :: (Eq a) => a -> a -> Property Bool
  eqP l r = pure (l == r)
  showP :: a -> String
  default showP :: (Show a) => a -> String
  showP = show

class (TestingEqShow a) => TestableType a where
  gen :: GenTotal a

-- | Supplies a 'Show' instance derived from 'showP'.
--
-- falsify's 'Show' instance for 'Fun' needs 'Show' on both parameters, and we
-- only ever have 'TestingEqShow'. Rather than reinterpret a @'Fun' a b@ at the
-- wrapped type after the fact, @GenFun@ generates at
-- @'Fun' ('ShowP' a) ('ShowP' b)@ from the start, so 'show' applies directly and
-- no coercion is involved. 'applyFunP' unwraps on the way back out.
newtype ShowP a = ShowP {unShowP :: a}

instance (TestingEqShow a) => Show (ShowP a) where
  show (ShowP a) = showP a

instance (Function a) => Function (ShowP a) where
  function = fmap (functionMap unShowP ShowP) . function

-- | Apply a generated function, wrapping and unwrapping the 'ShowP' it was
-- generated at. Both directions are ordinary newtype constructor applications.
applyFunP :: Fun (ShowP a) (ShowP b) -> a -> b
applyFunP f = unShowP . applyFun f . ShowP

genP :: (TestableType a) => Property a
genP = case gen of
  GenNENonFun g -> genWith (Just . showP) g
  GenFun f g -> f . applyFunP <$> genWith (Just . show) g
  GenEmpty _ -> discard

genNamed :: (TestableType a) => String -> Property a
genNamed nm = case gen of
  GenNENonFun g -> genWithNamed nm (Just . showP) g
  GenFun f g -> f . applyFunP <$> genWithNamed nm (Just . show) g
  GenEmpty _ -> discard

-- | Check a measured value against the expected one, showing both. For the assertions a worked
-- example makes, which no generic law-checking property covers.
expect :: (Eq a, Show a) => String -> a -> a -> Property ()
expect what want got = unless (got == want) (testFailed (what ++ ", found " ++ show got ++ ", expected " ++ show want))

-- | Check that two values are semantically equal, naming both sides so a failure says which law
-- broke and what the two sides came out as.
testEq :: (TestingEqShow a) => String -> String -> a -> String -> a -> Property ()
testEq nm sl l sr r = do
  isEq <- eqP l r
  unless isEq $
    testFailed $
      "Failed "
        ++ nm
        ++ ":\n"
        ++ sl
        ++ " = "
        ++ showP l
        ++ "\n"
        ++ sr
        ++ " = "
        ++ showP r

genWithNamed :: String -> (a -> Maybe String) -> Gen a -> Property a
genWithNamed nm f = genWith (fmap named . f)
  where
    named s = "for " ++ nm ++ ": " ++ s

-- | 'True' if a type's generator is non-empty. A pure check on 'TestableType's 'gen'. It
-- doesn't sample anything, so it is cheap to call as often as convenient, e.g. once in a
-- 'genSuchThat' predicate and again in the 'gen'\/'genNamed' call that produces a value.
isGenNonEmpty :: forall a. (TestableType a) => Bool
isGenNonEmpty = case gen @a of
  GenEmpty _ -> False
  _ -> True

-- | Resample @genKey@ (cheaply, within 'Gen') up to @maxTries@ times until @isUsable@ accepts
-- the draw, before ever asking 'Property' to commit to a choice.
--
-- A 'Property'-level 'discard' restarts the whole property and can trip falsify's discard-ratio
-- limit, aborting the run. So when a later dependent draw (e.g. \"a morphism out of this
-- object\") is likely to be empty for a bad choice, reject that choice here. After @maxTries@ the
-- last draw is returned anyway, and the caller's own 'discard' handles it.
genSuchThat :: Gen key -> (key -> Bool) -> Gen key
genSuchThat genKey isUsable = go maxTries
  where
    go n = do
      k <- genKey
      if isUsable k || n <= (0 :: Int) then pure k else go (n - 1)

-- | How many times 'genSuchThat' resamples before giving up. There is no principled formula
-- for this, since it depends on how sparse the requirement being searched for is, which
-- 'genSuchThat' cannot know in advance. 100 is comfortably more than the number of candidates a
-- small test object palette usually offers, so a single unlucky pick is very unlikely to exhaust
-- it. It is still cheap, since each attempt is a plain 'Gen' sample and not a 'Property'-level
-- 'discard'.
maxTries :: Int
maxTries = 100

-- | 'genOb', but resampled (see 'genSuchThat') until @isUsable@ accepts the object.
genObSuchThat :: forall k. (Testable k) => (Some k -> Bool) -> Property (Some k)
genObSuchThat = genWith (Just . show) . genSuchThat (genSome @k)

type SomeProfunctorElt :: (j +-> k) -> Type
data SomeProfunctorElt p where
  SomeP :: (TestOb a, TestOb b) => p a b -> SomeProfunctorElt p

someP :: forall {k} {j} (p :: k +-> j) a b. (Profunctor p, TestObIsOb j, TestObIsOb k) => p a b -> SomeProfunctorElt p
someP p = SomeP p \\ p

instance
  (forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestingEqShow (p a b), Testable k, Testable j)
  => Show (SomeProfunctorElt p)
  where
  show (SomeP @a @b p) = showP p ++ " @" ++ showOb @k @a ++ " @" ++ showOb @j @b

type TestableTypeP :: (j +-> k) -> Constraint
class (forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestableType (p a b)) => TestableTypeP (p :: j +-> k)
instance (forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestableType (p a b)) => TestableTypeP (p :: j +-> k)

type TestableProfunctor :: forall {j} {k}. j +-> k -> Constraint
class
  (Testable j, Testable k, Profunctor p, forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestingEqShow (p a b)) =>
  TestableProfunctor (p :: j +-> k)
  where
  -- | The default implementation generates types @a@ and @b@ and then generates a value of type @p a b@.
  -- But that can cause too many discarded tests.
  genProfunctorElt :: String -> Property (SomeProfunctorElt p)
  default genProfunctorElt :: (TestableTypeP p) => String -> Property (SomeProfunctorElt p)
  genProfunctorElt nm = do
    Some @a <- genOb
    Some @b <- genOb
    p <- genNamed @(p a b) nm
    pure $ SomeP p

-- | A kind whose objects can be enumerated and displayed.
class (forall (a :: k). (TestOb a) => Ob' a, TestableProfunctor (Hom k), TestableTypeP (Hom k), CategoryOf k) => Testable k where
  type TestOb (a :: k) :: GHC.Constraint
  type TestOb a = Ob a
  showOb :: forall (a :: k). (TestOb a) => String
  genSome :: Gen (Some k)

  -- | The palette for properties whose cost grows steeply with object size: in practice those
  -- that enumerate an internal hom, which is brute force over tables and doubly exponential (an
  -- object with hom-sizes @[2,4,2,4]@ has the hom into it at @[1024,256,1024,256]@). Defaults to
  -- 'genSome'. Override it only when 'genSome' draws objects too big for
  -- 'Proarrow.Testing.Laws.testClosed' to terminate.
  --
  -- An instance that wraps another kind's palette must forward this too, as the wrapper instances
  -- below do, or 'Proarrow.Testing.Laws.testClosed' silently gets the wide one.
  genSomeSmall :: Gen (Some k)
  genSomeSmall = genSome

  {-# MINIMAL showOb, genSome #-}

genOb :: (Testable k) => Property (Some k)
genOb = genWith (Just . show) genSome

-- | 'genOb' from the small palette. See 'genSomeSmall'.
genObSmall :: (Testable k) => Property (Some k)
genObSmall = genWith (Just . show) genSomeSmall

instance (TestableProfunctor p) => TestableProfunctor (Op p) where
  genProfunctorElt nm = do
    SomeP p <- genProfunctorElt @p nm
    pure $ SomeP (Op p)
instance (Testable k) => Testable (OPPOSITE k) where
  type TestOb a = (Is OP a, TestOb (UN OP a))
  showOb @(OP a) = "OP (" ++ showOb @k @a ++ ")"
  genSome = mapSome OP <$> genSome
  genSomeSmall = mapSome OP <$> genSomeSmall

-- | The 'PROD' wrapper changes only which tensor a kind carries, so everything transports across it.
instance (TestableProfunctor p) => TestableProfunctor (Prod p) where
  genProfunctorElt nm = do
    SomeP p <- genProfunctorElt @p nm
    pure $ SomeP (Prod p)

instance (Testable k) => Testable (PROD k) where
  type TestOb a = (Is PR a, TestOb (UN PR a))
  showOb @(PR a) = "PR (" ++ showOb @k @a ++ ")"
  genSome = mapSome PR <$> genSome
  genSomeSmall = mapSome PR <$> genSomeSmall

instance TestableProfunctor Unit
instance Testable () where
  showOb = "()"
  genSome = pure (Some @'())

instance (TestableProfunctor p, TestableProfunctor q) => TestableProfunctor (p :**: q) where
  genProfunctorElt nm = do
    SomeP p <- genProfunctorElt @p (nm ++ "_0")
    SomeP q <- genProfunctorElt @q (nm ++ "_1")
    pure $ SomeP (p :**: q)
instance (Testable j, Testable k) => Testable (j, k) where
  type TestOb a = (a ~ '(Fst @ a, Snd @ a), TestOb (Fst @ a), TestOb (Snd @ a))
  showOb @'(a, b) = "(" ++ showOb @j @a ++ ", " ++ showOb @k @b ++ ")"
  genSome = do
    Some @a <- genSome @j
    Some @b <- genSome @k
    pure $ Some @'(a, b)
  genSomeSmall = do
    Some @a <- genSomeSmall @j
    Some @b <- genSomeSmall @k
    pure $ Some @'(a, b)

class (TestOb a) => TestOb' a
instance (TestOb a) => TestOb' a

class (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k
instance (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k

-- | Recover @'Ob' a@ from @'TestOb' a@ (the 'Testable' superclass entailment), packaged as a
-- function so that call sites with other quantified givens in scope (e.g. the comonoid supply of a
-- 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' category, whose head has @Ob@ as a
-- superclass) don't have to rely on GHC expanding superclasses of quantified-constraint heads.
-- With such a given in scope, @\\r -> r@ at this type fails with "Could not deduce Ob a", while
-- the same lambda compiles without it (cf. 'Proarrow.Testing.Laws.testSymMonoidal_' versus
-- 'Proarrow.Testing.Laws.testCopyDiscard_').
obFromTestOb :: forall {k} (a :: k) r. (Testable k, TestOb a) => ((Ob a) => r) -> r
-- Seen on GHC 9.10.3, likely a solver limitation. Worth retrying without this helper after a
-- GHC upgrade.
obFromTestOb r = r

-- * Objecthood witnesses

-- | How 'TestOb' is closed under the structure a law-checker is about.
--
-- Every law-checker in "Proarrow.Testing.Laws" that needs one takes it as an explicit rank-2 argument, since in
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

data Some k where
  Some :: forall {k} a. (TestOb (a :: k)) => Some k

mapSome :: forall {j} {k}. forall (f :: j -> k) -> (forall a. (TestOb a) => TestOb' (f a)) => Some j -> Some k
mapSome f (Some @a) = Some @(f a)

class MkSomeList (as :: [k]) where
  mkSomeList :: [Some k]
instance MkSomeList '[] where
  mkSomeList = []
instance (TestOb (a :: k), MkSomeList as) => MkSomeList (a ': as) where
  mkSomeList = Some @a : mkSomeList @k @as
instance (Testable k) => Show (Some k) where
  show (Some @a) = showOb @k @a

someElem :: (Show a) => [a] -> Property a
someElem = someElemWith show

someElemNamed :: (Show a) => String -> [a] -> Property a
someElemNamed nm = someElemWith (\a -> "for " ++ nm ++ ": " ++ show a)

someElemWith :: (a -> String) -> [a] -> Property a
someElemWith _ [] = discard
someElemWith f (x : xs) = genWith (Just . f) (elem (x :| xs))

genSomeDef :: forall {k} (obs :: [k]). (Testable k, MkSomeList obs) => Gen (Some k)
genSomeDef = genSomeList "the palette is empty" (mkSomeList @k @obs)

-- | The palette of a category that already knows its own objects: @'Proarrow.Category.Enriched.Thin.Objects' k@
-- is the list 'genSomeDef' would otherwise be given by hand, and writing it twice lets the two
-- drift apart. Only for kinds that really are finite categories. A palette like \"four
-- cardinalities out of infinitely many\" is a sample, not an enumeration, and has to stay
-- hand-picked.
genSomeFinite :: forall k. (Enumerable k, TestObIsOb k) => Gen (Some k)
genSomeFinite = genSomeList "the category has no objects" (foreachOb @k \ @a -> [Some @a])

genSomeList :: String -> [Some k] -> Gen (Some k)
genSomeList what [] = error ("genSome: " ++ what)
genSomeList _ (x : xs) = elem (x :| xs)

-- | A generator for a two-component value: if either component has no values then neither does the
-- pair, and otherwise the two are drawn independently.
--
-- 'GenEmpty' carries its proof of emptiness as a function out of the empty type, so reusing a
-- component's proof for the pair means getting at that component first. Hence the two projections
-- alongside the constructor.
genBoth
  :: forall a b c. (TestableType a, TestableType b) => (a -> b -> c) -> (c -> a) -> (c -> b) -> GenTotal c
genBoth mk outl outr = case (gen @a, gen @b) of
  (GenEmpty f, _) -> GenEmpty (\c -> f (outl c))
  (_, GenEmpty g) -> GenEmpty (\c -> g (outr c))
  (GenNonEmpty ga, GenNonEmpty gb) -> GenNonEmpty (liftA2 mk ga gb)

optGen :: [a] -> GenTotal a
optGen [] = error "optGen: empty list"
optGen (x : xs) = GenNonEmpty (elem (x :| xs))

-- | Draw from a finitary profunctor's own enumeration, an empty hom-set being 'GenEmpty' rather than
-- an error: a profunctor built by the library can be empty at a pair of objects with nothing wrong.
-- For a hand-written fixture prefer a palette of its own. 'Proarrow.Testing.Laws.testFinitary'
-- says why a generator that /is/ the enumeration makes the round-trip law vacuous.
genElements :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (Finitary p, Ob a, Ob b) => GenTotal (p a b)
genElements = case elements @p @a @b of
  [] -> GenEmpty \_ -> error "genElements: no elements at these objects"
  xs -> optGen xs

oneElem :: a -> GenTotal a
oneElem x = GenNonEmpty (pure x)

instance (TestableType a, TestingEqShow b) => TestingEqShow (a -> b) where
  eqP = eqHask
  showP _ = "<function>"

instance (Function a, TestableType a, TestableType b) => TestableType (a -> b) where
  gen = case gen @b of
    GenEmpty absurd -> case gen @a of
      GenEmpty absurda -> oneElem absurda
      GenNonEmpty g -> GenEmpty \ab -> absurd (ab (minimalValue g))
    GenNonEmpty gb -> GenFun id (fun (ShowP <$> gb))

eqHask :: (TestableType a, TestingEqShow b) => (a -> b) -> (a -> b) -> Property Bool
eqHask l r =
  case gen of
    GenEmpty _ -> pure True -- There can only be one function of a type with no values
    GenNonEmpty ga -> do
      a <- genWith (Just . showP) ga
      eqP (l a) (r a)

instance (TestableType (p a b)) => TestableType (Prod p (PR a) (PR b)) where
  gen = invmap Prod unProd gen
instance (TestingEqShow (p a b)) => TestingEqShow (Prod p (PR a) (PR b)) where
  eqP (Prod l) (Prod r) = eqP l r
  showP (Prod p) = "Prod (" ++ showP p ++ ")"

instance (TestableType (p b a)) => TestableType (Op p (OP a) (OP b)) where
  gen = invmap Op unOp gen
instance (TestingEqShow (p b a)) => TestingEqShow (Op p (OP a) (OP b)) where
  eqP (Op l) (Op r) = eqP l r
  showP (Op p) = "Op (" ++ showP p ++ ")"

-- | The elements of 'Star' and 'Costar' are arrows, and are compared, shown and drawn as those.
instance (TestingEqShow (a ~> f b)) => TestingEqShow (Star f a b) where
  eqP (Star l) (Star r) = eqP l r
  showP (Star f) = showP f

instance (Ob b, TestableType (a ~> f b)) => TestableType (Star f a b) where
  gen = invmap Star (\(Star f) -> f) gen

instance (TestingEqShow (f a ~> b)) => TestingEqShow (Costar f a b) where
  eqP (Costar l) (Costar r) = eqP l r
  showP (Costar f) = showP f

instance (Ob a, TestableType (f a ~> b)) => TestableType (Costar f a b) where
  gen = invmap Costar (\(Costar f) -> f) gen

instance (TestableType (a ~> (f Rep.@ b)), Ob b) => TestableType (Rep f a b) where
  gen = invmap Rep unRep (gen @(a ~> f Rep.@ b))
instance (TestingEqShow (a ~> (f Rep.@ b)), Ob b) => TestingEqShow (Rep f a b) where
  eqP (Rep l) (Rep r) = eqP l r
  showP (Rep p) = showP p

instance (TestingEqShow (catk a1 b1), TestingEqShow (catj a2 b2)) => TestingEqShow ((catk :**: catj) '(a1, a2) '(b1, b2)) where
  eqP (l1 :**: l2) (r1 :**: r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (l1 :**: l2) = "(" ++ showP l1 ++ ") :**: (" ++ showP l2 ++ ")"
instance (TestableType (catk a1 b1), TestableType (catj a2 b2)) => TestableType ((catk :**: catj) '(a1, a2) '(b1, b2)) where
  gen = genBoth (:**:) fstK sndK

-- | An element of a product of profunctors is a pair of elements.
instance (TestingEqShow (p a b), TestingEqShow (q a b)) => TestingEqShow ((p :*: q) a b) where
  eqP (l1 :*: l2) (r1 :*: r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (l :*: r) = "(" ++ showP l ++ ") :*: (" ++ showP r ++ ")"

instance (TestableType (p a b), TestableType (q a b)) => TestableType ((p :*: q) a b) where
  gen = genBoth (:*:) fstP sndP

instance
  (TestableProfunctor p, TestableProfunctor q, TestableTypeP p, TestableTypeP q)
  => TestableProfunctor (p :*: q)

-- | An element of a coproduct of profunctors is an element of one side, tagged.
instance (TestingEqShow (p a b), TestingEqShow (q a b)) => TestingEqShow ((p :+: q) a b) where
  eqP (InjL l) (InjL r) = eqP l r
  eqP (InjR l) (InjR r) = eqP l r
  eqP _ _ = pure False
  showP (InjL l) = "InjL (" ++ showP l ++ ")"
  showP (InjR r) = "InjR (" ++ showP r ++ ")"

instance (TestableType (p a b), TestableType (q a b)) => TestableType ((p :+: q) a b) where
  gen = case (gen @(p a b), gen @(q a b)) of
    (GenEmpty f, GenEmpty g) -> GenEmpty \case InjL l -> f l; InjR r -> g r
    (GenEmpty _, GenNonEmpty gr) -> GenNonEmpty (InjR <$> gr)
    (GenNonEmpty gl, GenEmpty _) -> GenNonEmpty (InjL <$> gl)
    (GenNonEmpty gl, GenNonEmpty gr) -> GenNonEmpty (oneof ((InjL <$> gl) :| [InjR <$> gr]))

instance
  (TestableProfunctor p, TestableProfunctor q, TestableTypeP p, TestableTypeP q)
  => TestableProfunctor (p :+: q)

-- | A 'Tabulated' value is its index, so equality and display are the index's.
instance TestingEqShow (Tabulated t lm rm a b) where
  eqP (Tabulated i) (Tabulated j) = pure (i == j)
  showP (Tabulated i) = show i

instance
  ( Testable j
  , Testable k
  , FiniteCat j
  , FiniteCat k
  , KnownTables j k lm rm
  , TestOb (a :: k)
  , TestOb (b :: j)
  )
  => TestableType (Tabulated t lm rm a b)
  where
  gen = obFromTestOb @a (obFromTestOb @b (genElements @(Tabulated t lm rm)))

instance
  ( Testable j
  , Testable k
  , FiniteCat j
  , FiniteCat k
  , KnownTables j k lm rm
  )
  => TestableProfunctor (Tabulated t lm rm :: j +-> k)

-- | The terminal profunctor has one element at every pair of objects.
instance TestingEqShow (TerminalProfunctor a b) where
  -- forcing is the one thing left to check
  eqP l r = l `seq` r `seq` pure True
  showP _ = "TerminalProfunctor"

instance (Testable j, Testable k, TestOb (a :: k), TestOb (b :: j)) => TestableType (TerminalProfunctor a b) where
  gen = obFromTestOb @a (obFromTestOb @b (oneElem TerminalProfunctor))

instance (Testable j, Testable k) => TestableProfunctor (TerminalProfunctor :: j +-> k)

-- | An element of the Yoneda embedding is an arrow into @x@ paired with an arrow out of @b@, so it
-- is testable wherever both categories are. So a representable can be used as a test fixture, at
-- either variance.
instance
  (Testable j, Testable k, TestOb (a :: k), TestOb (x :: k), TestOb (b :: j), TestOb (c :: j))
  => TestingEqShow (Yo x (OP b) a c)
  where
  eqP (Yo f h) (Yo g i) = liftA2 (&&) (eqP f g) (eqP h i)
  showP (Yo f h) = "Yo (" ++ showP f ++ ") (" ++ showP h ++ ")"

instance
  (Testable j, Testable k, TestOb (a :: k), TestOb (x :: k), TestOb (b :: j), TestOb (c :: j))
  => TestableType (Yo x (OP b) a c)
  where
  gen = genBoth Yo (\(Yo l _) -> l) (\(Yo _ r) -> r)

instance (Testable j, Testable k, TestOb (x :: k), TestOb (b :: j)) => TestableProfunctor (Yo x (OP b))

-- | A sieve is a table of booleans over the points of the representable, and 'Finitary' numbers the
-- sieves at each pair of objects. So a sieve can be generated by picking one, and compared and
-- shown by its table. Without this, nothing that quantifies over sieves as elements of a
-- profunctor (such as 'Proarrow.Testing.Laws.propNaturalTransformation') can run at 'Sieve'.
--
-- Drawing one enumerates /every/ sieve at that pair of objects, a count exponential in the size of
-- the representable, so this is the generator to look at first if a suite gets slow.
--
-- The 'TestOb' constraints pin @j@ and @k@, which @'Sieve' a b@ does not mention.
instance (FiniteCat j, FiniteCat k, TestOb (a :: k), TestOb (b :: j)) => TestingEqShow (Sieve a b) where
  eqP s t = pure (sieveTable s == sieveTable t)
  showP s = show (sieveTable s)

instance
  (Testable j, Testable k, FiniteCat j, FiniteCat k, TestOb (a :: k), TestOb (b :: j))
  => TestableType (Sieve a b)
  where
  gen = obFromTestOb @a (obFromTestOb @b (genElements @(Sieve :: j +-> k)))

instance (Testable j, Testable k, FiniteCat j, FiniteCat k) => TestableProfunctor (Sieve :: j +-> k)

-- | An element of the internal hom is a natural transformation out of a weight, which 'Finitary'
-- numbers; compare and show it by that number, as 'Tabulated' is. Drawing one enumerates them
-- all, so an exponential is expensive to quantify over.
instance
  (Finitary p, Finitary q, FiniteCat j, FiniteCat k, TestOb (a :: k), TestOb (b :: j))
  => TestingEqShow ((p :~>: q) a b)
  where
  -- matching on 'Exp' brings the objects into scope, as it does for 'Sieve'
  eqP x@Exp{} y = pure (toIndex @(p :~>: q) x == toIndex y)
  showP x@Exp{} = show (toIndex @(p :~>: q) x)

instance
  (Testable j, Testable k, Finitary p, Finitary q, FiniteCat j, FiniteCat k, TestOb (a :: k), TestOb (b :: j))
  => TestableType ((p :~>: q) a b)
  where
  gen = obFromTestOb @a (obFromTestOb @b (genElements @(p :~>: q)))

instance
  (Testable j, Testable k, Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => TestableProfunctor (p :~>: q :: j +-> k)

-- | A natural transformation between finitary profunctors, compared and shown by its table and
-- drawn from 'natTransformations'. The hom-sets of a category of finitary profunctors, with or
-- without the 'SUBCAT' wrapper.
instance (Finitary p, Finitary q, FiniteCat j, FiniteCat k) => TestingEqShow (Prof (p :: j +-> k) q) where
  eqP (Prof f) (Prof g) = pure (natTable @p @q f == natTable @p @q g)
  showP (Prof f) = show (natTable @p @q f)

instance (Finitary p, Finitary q, FiniteCat j, FiniteCat k) => TestableType (Prof (p :: j +-> k) q) where
  gen = case natTransformations @p @q of
    [] -> GenEmpty \_ -> error "no natural transformations between these profunctors"
    fs -> optGen fs

-- | The right Kan lift and extension of finitary profunctors, compared and shown by index, as the
-- internal hom is.
instance
  (Testable j, Testable k, Finitary w, Finitary p, FiniteCat i, FiniteCat j, TestOb (a :: k), TestOb (b :: j))
  => TestingEqShow (Rift (OP (w :: k +-> i)) p a b)
  where
  eqP x@Rift{} y = pure (toIndex @(Rift (OP w) p) x == toIndex y)
  showP x@Rift{} = show (toIndex @(Rift (OP w) p) x)

instance
  (Testable j, Testable k, Finitary w, Finitary p, FiniteCat i, FiniteCat j, TestOb (a :: k), TestOb (b :: j))
  => TestableType (Rift (OP (w :: k +-> i)) p a b)
  where
  gen = obFromTestOb @a (obFromTestOb @b (genElements @(Rift (OP w) p)))

instance
  (Testable j, Testable k, Finitary w, Finitary p, FiniteCat i, FiniteCat j)
  => TestableProfunctor (Rift (OP (w :: k +-> i)) p :: j +-> k)

instance
  (Testable j, Testable k, Finitary v, Finitary p, FiniteCat i, FiniteCat k, TestOb (a :: k), TestOb (b :: j))
  => TestingEqShow (Ran (OP (v :: i +-> j)) p a b)
  where
  eqP x@Ran{} y = pure (toIndex @(Ran (OP v) p) x == toIndex y)
  showP x@Ran{} = show (toIndex @(Ran (OP v) p) x)

instance
  (Testable j, Testable k, Finitary v, Finitary p, FiniteCat i, FiniteCat k, TestOb (a :: k), TestOb (b :: j))
  => TestableType (Ran (OP (v :: i +-> j)) p a b)
  where
  gen = obFromTestOb @a (obFromTestOb @b (genElements @(Ran (OP v) p)))

instance
  (Testable j, Testable k, Finitary v, Finitary p, FiniteCat i, FiniteCat k)
  => TestableProfunctor (Ran (OP (v :: i +-> j)) p :: j +-> k)

-- | A closed sieve is a sieve, and is compared and shown as one. Drawing one is dearer still than
-- drawing a sieve: the closed ones are found by taking the 'closure' of every sieve at the pair.
instance (FiniteCat j, FiniteCat k, TestOb (a :: k), TestOb (b :: j)) => TestingEqShow (ClosedSieve t a b) where
  eqP (ClosedSieve s) (ClosedSieve u) = eqP s u
  showP (ClosedSieve s) = showP s

instance
  ( Testable j
  , Testable k
  , HasFiniteCovers t k
  , FiniteCat j
  , FiniteCat k
  , TestOb (a :: k)
  , TestOb (b :: j)
  )
  => TestableType (ClosedSieve t a b)
  where
  gen = obFromTestOb @a (obFromTestOb @b (genElements @(ClosedSieve t :: j +-> k)))

instance
  (Testable j, Testable k, HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => TestableProfunctor (ClosedSieve t :: j +-> k)

-- | Compared by 'samePlus' and shown by 'plusTable'. See 'Plus' for what a value stands for.
instance
-- as for 'Sieve', the 'TestOb's are what pin @j@ and @k@
  (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k, TestOb (a :: k), TestOb (b :: j))
  => TestingEqShow (Plus t p a b)
  where
  eqP x y = pure (samePlus x y)
  showP x = show (plusTable x)

instance
  (Testable j, Testable k, HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k, TestOb (a :: k), TestOb (b :: j))
  => TestableType (Plus t p a b)
  where
  gen = obFromTestOb @a (obFromTestOb @b (genElements @(Plus t p :: j +-> k)))

instance
  (Testable j, Testable k, HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k)
  => TestableProfunctor (Plus t p :: j +-> k)

-- | A hom-set of a full subcategory of finitary profunctors ('FINITARY', or the sheaves of
-- "Proarrow.Category.Enriched.Finitary.Sheaf") is enumerable, by 'natTransformations', so it can
-- be generated. Without that a category of profunctors would not be testable at all. Equality and
-- display go through the table of indices, there being nothing else to see of a natural
-- transformation. (The table is cheaper than the index into 'elements' would be, which has to
-- search for it.)
instance
  (Finitary p, Finitary q, FiniteCat j, FiniteCat k)
  => TestingEqShow (Sub Prof (SUB p :: SUBCAT (ob :: OB (j +-> k))) (SUB q))
  where
  eqP (Sub l) (Sub r) = eqP l r
  showP (Sub f) = showP f

instance
  (Finitary (Sub Prof :: CAT (SUBCAT ob)), Finitary p, Finitary q, FiniteCat j, FiniteCat k, ob p, ob q)
  => TestableType (Sub Prof (SUB p :: SUBCAT (ob :: OB (j +-> k))) (SUB q))
  where
  -- a hom-set is empty whenever @q@ runs out of elements where @p@ has some, and then the
  -- properties discard rather than fail
  gen = genElements @(Sub Prof) @(SUB p) @(SUB q)

instance (Ob a, Ob b) => TestableType (Unit a b) where
  gen = oneElem Unit
instance TestingEqShow (Unit a b) where
  showP _ = "Unit"

  -- a singleton, so equality is free; forcing is the one thing left to check
  eqP l r = l `seq` r `seq` pure True

sampleT :: forall t. (TestableType t) => IO (Maybe String)
sampleT = falsify $ do
  p <- genP @t
  traceM (showP p)

sampleP :: forall {j} {k} (p :: j +-> k). (Testable j, Testable k, TestableProfunctor p) => IO (Maybe String)
sampleP = falsify $ do
  p <- genProfunctorElt @p "p"
  traceShowM p

sampleK :: forall k. (Testable k) => IO (Maybe String)
sampleK = falsify @_ @() $ do
  Some @a <- genOb @k
  traceM $ showOb @k @a
