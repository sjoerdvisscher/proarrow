{-# LANGUAGE AllowAmbiguousTypes #-}

module Testable where

import Data.Kind (Constraint)
import Data.List.NonEmpty (NonEmpty (..))
import GHC.Exts qualified as GHC
import Test.Falsify.Generator (elem, Gen)
import Test.Tasty.Falsify (Property, discard, genWith)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), Profunctor (..), type (+->))
import Proarrow.Object (Ob')

class EnumAll a where
  enumAll :: [a]

class TestableType a where
  gen :: Maybe (Gen a)
  default gen :: (EnumAll a) => Maybe (Gen a)
  gen = optGen enumAll
  eqP :: a -> a -> Property Bool
  default eqP :: (Eq a) => a -> a -> Property Bool
  eqP l r = pure (l == r)
  showP :: a -> String
  default showP :: (Show a) => a -> String
  showP = show

genP :: TestableType a => Property a
genP = case gen of
  Just g -> genWith (Just . showP) g
  Nothing -> discard

type TestableProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Testable j, Testable k, Profunctor p, forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestableType (p a b)) => TestableProfunctor (p :: j +-> k)
instance (Testable j, Testable k, Profunctor p, forall a b. (TestOb (a :: k), TestOb (b :: j)) => TestableType (p a b)) => TestableProfunctor (p :: j +-> k)

class (forall (a :: k). (TestOb a) => Ob' a, TestableProfunctor ((~>) :: CAT k), CategoryOf k) => Testable k where
  type TestOb (a :: k) :: GHC.Constraint
  type TestOb a = Ob a
  showOb :: forall (a :: k). (TestOb a) => String
  genOb :: Property (Some k)

class (TestOb a) => TestOb' a
instance (TestOb a) => TestOb' a

class (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k
instance (forall (a :: k). (Ob a) => TestOb' a) => TestObIsOb k

data Some k where
  Some :: forall {k} a. (TestOb (a :: k)) => Some k

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

optGen :: [a] -> Maybe (Gen a)
optGen [] = Nothing
optGen (x : xs) = Just (elem (x :| xs))