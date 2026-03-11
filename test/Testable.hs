{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}

module Testable where

import Data.Kind (Constraint)
import Data.List.NonEmpty (NonEmpty (..))
import GHC.Exts qualified as GHC
import Test.Falsify.Generator (Fun, Gen, applyFun, elem)
import Test.Tasty.Falsify (Property, discard, genWith)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), type (+->), UN, Is)
import Proarrow.Object (Ob')
import Unsafe.Coerce (unsafeCoerce)
import Proarrow.Profunctor.Representable (Rep (..))
import Proarrow.Functor qualified as Rep
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))

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

class TestableType a where
  gen :: GenTotal a
  eqP :: a -> a -> Property Bool
  default eqP :: (Eq a) => a -> a -> Property Bool
  eqP l r = pure (l == r)
  showP :: a -> String
  default showP :: (Show a) => a -> String
  showP = show

newtype ShowP a = ShowP {unShowP :: a}
instance (TestableType a) => Show (ShowP a) where
  show (ShowP a) = showP a

showFun :: forall a b. (TestableType a, TestableType b) => Fun a b -> String
showFun = show . unsafeCoerce @(Fun a b) @(Fun (ShowP a) (ShowP b))

genP :: (TestableType a) => Property a
genP = case gen of
  GenNENonFun g -> genWith (Just . showP) g
  GenFun f g -> (f . applyFun) <$> genWith (Just . showFun) g
  GenEmpty _ -> discard

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

instance Testable k => Testable (OPPOSITE k) where
  type TestOb a = (Is OP a, TestOb (UN OP a))
  showOb @(OP a) = "OP (" ++ showOb @k @a ++ ")"
  genOb = mapSome OP <$> genOb

class (TestOb a) => TestOb' a
instance (TestOb a) => TestOb' a

class (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k
instance (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k

data Some k where
  Some :: forall {k} a. (TestOb (a :: k)) => Some k

mapSome :: forall {j} {k}. forall (f :: j -> k) -> (forall a. TestOb a => TestOb' (f a)) => Some j -> Some k
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

instance (TestableType (p b a)) => TestableType (Op p (OP a) (OP b)) where
  gen = invmap Op unOp gen
  eqP (Op l) (Op r) = eqP l r
  showP (Op p) = "Op (" ++ showP p ++ ")"

instance (TestableType (a ~> (f Rep.@ b)), Ob b) => TestableType (Rep f a b) where
  gen = invmap Rep unRep (gen @(a ~> f Rep.@ b))
  eqP (Rep l) (Rep r) = eqP l r
  showP (Rep p) = showP p