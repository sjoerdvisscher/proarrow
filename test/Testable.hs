{-# LANGUAGE AllowAmbiguousTypes #-}

module Testable where

import Data.Kind (Constraint)
import Data.List.NonEmpty (NonEmpty (..))
import GHC.Exts qualified as GHC
import Test.Falsify.Generator (elem)
import Test.Tasty.Falsify (Property, discard, genWith)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), Profunctor (..), type (+->))
import Proarrow.Object (Ob')

type TestableProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Testable j, Testable k, Profunctor p) => TestableProfunctor (p :: j +-> k) where
  genP :: (TestOb (a :: k), TestOb (b :: j)) => Property (p a b)
  eqP :: (TestOb (a :: k), TestOb (b :: j)) => p a b -> p a b -> Property Bool
  showP :: (TestOb (a :: k), TestOb (b :: j)) => p a b -> String

class (forall (a :: k). (TestOb a) => Ob' a, TestableProfunctor ((~>) :: CAT k)) => Testable k where
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