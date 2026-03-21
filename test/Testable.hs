{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}

module Testable where

import Data.Kind (Constraint)
import Data.List.NonEmpty (NonEmpty (..))
import GHC.Exts qualified as GHC
import Test.Falsify.Generator (Fun, Gen, applyFun, elem, Function, minimalValue, fun)
import Test.Tasty.Falsify (Property, discard, genWith)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor qualified as Rep
import Proarrow.Object (Ob')
import Proarrow.Profunctor.Representable (Rep (..))
import Unsafe.Coerce (unsafeCoerce)
import Proarrow.Category.Instance.Product ((:**:)(..), Fst, Snd)

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
flatten (GenFun f g) = (f . applyFun) <$> g
flatten (GenEmpty _) = error "flatten: Match on GenEmpty first"

pattern GenNonEmpty :: Gen a -> GenTotal a
pattern GenNonEmpty g <- (flatten -> g)
  where
    GenNonEmpty g = GenNENonFun g

{-# COMPLETE GenEmpty, GenNonEmpty #-}

class TestingEqShow a where
  eqP :: a -> a -> Property Bool
  default eqP :: (Eq a) => a -> a -> Property Bool
  eqP l r = pure (l == r)
  showP :: a -> String
  default showP :: (Show a) => a -> String
  showP = show

class TestingEqShow a => TestableType a where
  gen :: GenTotal a

newtype ShowP a = ShowP {unShowP :: a}
instance (TestingEqShow a) => Show (ShowP a) where
  show (ShowP a) = showP a

showFun :: forall a b. (TestingEqShow a, TestingEqShow b) => Fun a b -> String
showFun = show . unsafeCoerce @(Fun a b) @(Fun (ShowP a) (ShowP b))

genP :: (TestableType a) => Property a
genP = case gen of
  GenNENonFun g -> genWith (Just . showP) g
  GenFun f g -> (f . applyFun) <$> genWith (Just . showFun) g
  GenEmpty _ -> discard

genNamed :: (TestableType a) => String -> Property a
genNamed nm = case gen of
  GenNENonFun g -> genWith (Just . named . showP) g
  GenFun f g -> (f . applyFun) <$> genWith (Just . named . showFun) g
  GenEmpty _ -> discard
  where
    named s = "for " ++ nm ++ ": " ++ s

type TestableProfunctor :: forall {j} {k}. j +-> k -> Constraint
class
  (Testable j, Testable k, Profunctor p, forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestableType (p a b)) =>
  TestableProfunctor (p :: j +-> k)
instance
  (Testable j, Testable k, Profunctor p, forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestableType (p a b))
  => TestableProfunctor (p :: j +-> k)

class (forall (a :: k). (TestOb a) => Ob' a, TestableProfunctor ((~>) :: CAT k), CategoryOf k) => Testable k where
  type TestOb (a :: k) :: GHC.Constraint
  type TestOb a = Ob a
  showOb :: forall (a :: k). (TestOb a) => String
  genOb :: Property (Some k)

instance (Testable k) => Testable (OPPOSITE k) where
  type TestOb a = (Is OP a, TestOb (UN OP a))
  showOb @(OP a) = "OP (" ++ showOb @k @a ++ ")"
  genOb = mapSome OP <$> genOb

instance (Testable j, Testable k) => Testable (j, k) where
  type TestOb a = (a ~ '(Fst a, Snd a), TestOb (Fst a), TestOb (Snd a))
  showOb @'(a, b) = "(" ++ showOb @j @a ++ ", " ++ showOb @k @b ++ ")"
  genOb = do
    Some @a <- genOb @j
    Some @b <- genOb @k
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

someElemWith :: (a -> String) -> [a] -> Property a
someElemWith _ [] = discard
someElemWith f (x : xs) = genWith (Just . f) (elem (x :| xs))

genObDef :: forall {k} (obs :: [k]). (Testable k, MkSomeList obs) => Property (Some k)
genObDef = someElem (mkSomeList @k @obs)

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