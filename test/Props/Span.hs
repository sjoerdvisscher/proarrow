{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Span where

import Data.Foldable (toList)
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3)
import Data.Typeable ((:~:) (..))
import Test.Tasty (TestTree, testGroup)
import Prelude (Bool (..), Maybe (..), pure, zip, ($), (&&), (++), (<$>), (<*>), (||), (==))

import Proarrow.Category.Instance.Span (SPAN (..), Span (..))
import Proarrow.Category.Instance.FinSet (FINSET (..), unFinSet)
import Proarrow.Core (CategoryOf (..), UN, (//), (\\))

import Props
import Props.FinSet ()
import Testable
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableType (..)
  , TestingEqShow (..)
  , mapSome
  , pattern GenNonEmpty
  )
import Data.List (sort)

test :: TestTree
test =
  testGroup
    "Span(FinSet)"
    [ propCategory @(SPAN FINSET)
    , propMonoidal_ @(SPAN FINSET)
    , propSymMonoidal_ @(SPAN FINSET)
    , propClosed_ @(SPAN FINSET)
    , propStarAutonomous_ @(SPAN FINSET)
    , testMonoid_ @(SP (FS Nat0))
    , testMonoid_ @(SP (FS Nat1))
    , testMonoid_ @(SP (FS Nat2))
    , testMonoid_ @(SP (FS Nat3))
    , testComonoid_ @(SP (FS Nat0))
    , testComonoid_ @(SP (FS Nat1))
    , testComonoid_ @(SP (FS Nat2))
    , testComonoid_ @(SP (FS Nat3))
    ]

-- instance (Testable k, HasPushouts k, TestObIsOb k) => Testable (SPAN k) where
instance Testable (SPAN FINSET) where
  type TestOb a = Ob a
  showOb @a = showOb @_ @(UN SP a)
  eqOb @a @b = (\Refl -> Refl) <$> eqOb @_ @(UN SP a) @(UN SP b)
  genSome = mapSome SP <$> genSome

-- instance (Ob a, Ob b, Testable k, TestObIsOb k) => TestingEqShow (Span a (b :: SPAN k)) where
instance (Ob a, Ob b) => TestingEqShow (Span a (b :: SPAN FINSET)) where
  eqP (Span @c1 l1 r1) (Span @c2 l2 r2) =
    l1 //
      l2 //
        case eqOb @_ @c1 @c2 of
          Just Refl -> do
            eql <- eqP l1 l2
            eqr <- eqP r1 r2
            let hasIso = sort (zip (toList (unFinSet l1)) (toList (unFinSet r1))) == sort (zip (toList (unFinSet l2)) (toList (unFinSet r2)))
            pure $ (eql && eqr) || hasIso
          Nothing -> pure False
  showP (Span @c l r) = "Span @(" ++ showOb @_ @c ++ ") (" ++ showP l ++ ") (" ++ showP r ++ ")" \\ l

-- instance (TestOb a, TestOb b, Testable k, TestObIsOb k) => TestableType (Span a (b :: SPAN k)) where
instance (TestOb a, TestOb b) => TestableType (Span a (b :: SPAN FINSET)) where
  gen = GenNonEmpty $ loop
    where
      loop = do
        Some @c <- genSome @_
        case (gen @(c ~> UN SP a), gen @(c ~> UN SP b)) of
          (GenEmpty _, _) -> loop
          (_, GenEmpty _) -> loop
          (GenNonEmpty l, GenNonEmpty r) -> Span <$> l <*> r
