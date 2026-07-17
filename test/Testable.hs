{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}

module Testable where

import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Typeable (Typeable, eqT, (:~:) (..))
import GHC.Exts qualified as GHC
import Test.Falsify.Generator (Fun, Function, Gen, applyFun, elem, fun, minimalValue, oneof)
import Test.Tasty.Falsify (Property, discard, genWith)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Control.Applicative (Alternative (..))
import Control.Monad (ap)
import Debug.Trace (traceM, traceShowM)
import Proarrow.Category.Instance.Product (Fst, Snd, (:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Hom, Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (type (@))
import Proarrow.Functor qualified as Rep
import Proarrow.Object (Ob')
import Proarrow.Profunctor.Representable (Rep (..))
import Test.Falsify.Interactive (falsify)
import Unsafe.Coerce (unsafeCoerce)

data GenTotal a where
  GenEmpty :: ~(forall x. a -> x) -> GenTotal a
  GenNENonFun :: Gen a -> GenTotal a
  GenFun :: (TestableType a, TestableType b) => ((a -> b) -> p) -> Gen (Fun a b) -> GenTotal p

invmap :: (a -> b) -> (b -> a) -> GenTotal a -> GenTotal b
invmap _ f' (GenEmpty g) = GenEmpty (g . f')
invmap f _ (GenNENonFun g) = GenNENonFun (fmap f g)
invmap f _ (GenFun f' g) = GenFun (f . f') g

flatten :: GenTotal a -> Gen a
flatten (GenNENonFun g) = g
flatten (GenFun f g) = f . applyFun <$> g
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

newtype ShowP a = ShowP {unShowP :: a}
instance (TestingEqShow a) => Show (ShowP a) where
  show (ShowP a) = showP a

showFun :: forall a b. (TestingEqShow a, TestingEqShow b) => Fun a b -> String
showFun = show . unsafeCoerce @(Fun a b) @(Fun (ShowP a) (ShowP b))

genP :: (TestableType a) => Property a
genP = case gen of
  GenNENonFun g -> genWith (Just . showP) g
  GenFun f g -> f . applyFun <$> genWith (Just . showFun) g
  GenEmpty _ -> discard

genNamed :: (TestableType a) => String -> Property a
genNamed nm = case gen of
  GenNENonFun g -> genWithNamed nm (Just . showP) g
  GenFun f g -> f . applyFun <$> genWithNamed nm (Just . showFun) g
  GenEmpty _ -> discard

genWithNamed :: String -> (a -> Maybe String) -> Gen a -> Property a
genWithNamed nm f = genWith (fmap named . f)
  where
    named s = "for " ++ nm ++ ": " ++ s

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

class (forall (a :: k). (TestOb a) => Ob' a, TestableProfunctor (Hom k), TestableTypeP (Hom k), CategoryOf k) => Testable k where
  type TestOb (a :: k) :: GHC.Constraint
  type TestOb a = Ob a
  showOb :: forall (a :: k). (TestOb a) => String
  eqOb :: (TestOb (a :: k), TestOb b) => Maybe (a :~: b)
  default eqOb :: forall a b. (TestOb (a :: k), TestOb b, Typeable a, Typeable b) => Maybe (a :~: b)
  eqOb = eqT @a @b
  genSome :: Gen (Some k)

genOb :: (Testable k) => Property (Some k)
genOb = genWith (Just . show) genSome

instance (TestableProfunctor p) => TestableProfunctor (Op p) where
  genProfunctorElt nm = do
    SomeP p <- genProfunctorElt @p nm
    pure $ SomeP (Op p)
instance (Testable k) => Testable (OPPOSITE k) where
  type TestOb a = (Is OP a, TestOb (UN OP a))
  showOb @(OP a) = "OP (" ++ showOb @k @a ++ ")"
  eqOb @(OP a) @(OP b) = fmap (\Refl -> Refl) $ eqOb @k @a @b
  genSome = mapSome OP <$> genSome

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
  eqOb @'(a1, a2) @'(b1, b2) = case (eqOb @j @a1 @b1, eqOb @k @a2 @b2) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  genSome = do
    Some @a <- genSome @j
    Some @b <- genSome @k
    pure $ Some @'(a, b)

class (TestOb a) => TestOb' a
instance (TestOb a) => TestOb' a

class (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k
instance (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k

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
genSomeDef = case mkSomeList @k @obs of
  [] -> error "genSomeDef: empty list"
  (x : xs) -> elem (x :| xs)

optGen :: [a] -> GenTotal a
optGen [] = error "optGen: empty list"
optGen (x : xs) = GenNonEmpty (elem (x :| xs))

one :: a -> GenTotal a
one x = GenNonEmpty (pure x)

instance (TestableType a, TestingEqShow b) => TestingEqShow (a -> b) where
  eqP = eqHask
  showP _ = "<function>"

instance (Function a, TestableType a, TestableType b) => TestableType (a -> b) where
  gen = case gen @b of
    GenEmpty absurd -> case gen @a of
      GenEmpty absurda -> one absurda
      GenNonEmpty g -> GenEmpty \ab -> absurd (ab (minimalValue g))
    GenNonEmpty gb -> GenFun id (fun gb)

eqHask :: (TestableType a, TestingEqShow b) => (a -> b) -> (a -> b) -> Property Bool
eqHask l r =
  case gen of
    GenEmpty _ -> pure True -- There can only be one function of a type with no values
    GenNonEmpty ga -> do
      a <- genWith (Just . showP) ga
      eqP (l a) (r a)

instance (TestableType (p b a)) => TestableType (Op p (OP a) (OP b)) where
  gen = invmap Op unOp gen
instance (TestingEqShow (p b a)) => TestingEqShow (Op p (OP a) (OP b)) where
  eqP (Op l) (Op r) = eqP l r
  showP (Op p) = "Op (" ++ showP p ++ ")"

instance (TestableType (a ~> (f Rep.@ b)), Ob b) => TestableType (Rep f a b) where
  gen = invmap Rep unRep (gen @(a ~> f Rep.@ b))
instance (TestingEqShow (a ~> (f Rep.@ b)), Ob b) => TestingEqShow (Rep f a b) where
  eqP (Rep l) (Rep r) = eqP l r
  showP (Rep p) = showP p

instance (TestingEqShow (catk a1 b1), TestingEqShow (catj a2 b2)) => TestingEqShow ((catk :**: catj) '(a1, a2) '(b1, b2)) where
  eqP (l1 :**: l2) (r1 :**: r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (l1 :**: l2) = "(" ++ showP l1 ++ ") :**: (" ++ showP l2 ++ ")"
instance (TestableType (catk a1 b1), TestableType (catj a2 b2)) => TestableType ((catk :**: catj) '(a1, a2) '(b1, b2)) where
  gen = case (gen, gen) of
    (GenEmpty f, _) -> GenEmpty \(l :**: _) -> f l
    (_, GenEmpty f) -> GenEmpty \(_ :**: r) -> f r
    (GenNonEmpty ga, GenNonEmpty gb) -> GenNonEmpty $ liftA2 (:**:) ga gb

instance (Ob a, Ob b) => TestableType (Unit a b) where
  gen = one Unit
instance TestingEqShow (Unit a b) where
  showP _ = "Unit"
  eqP _ _ = pure True

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
