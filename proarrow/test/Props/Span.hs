{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Span where

import Data.Foldable (toList)
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3)
import Data.Typeable ((:~:) (..))
import Test.Tasty (TestTree, testGroup)
import Prelude (Bool (..), Maybe (..), pure, zip, ($), (&&), (++), (<$>), (<*>), (==), (||))

import Proarrow.Category.Instance.FinSet (FINSET (..), unFinSet)
import Proarrow.Category.Instance.Span (SPAN (..), Span (..))
import Proarrow.Core (CAT, CategoryOf (..), UN, (//), (\\))

import Data.List (sort)
import Proarrow.Testing
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , mapSome
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Props.FinSet (eqFinSet)

test :: TestTree
test =
  testGroup
    "Span(FinSet)"
    [ testCategory @(SPAN FINSET)
    , testDagger @(SPAN FINSET)
    , testMonoidal_ @(SPAN FINSET)
    , testMonoidalHom_ @(SPAN FINSET)
    , testSymMonoidal_ @(SPAN FINSET)
    , testClosed_ @(SPAN FINSET)
    , testStarAutonomous_ @(SPAN FINSET)
    , testCompactClosed_ @(SPAN FINSET)
    , testCopyDiscard_ @(SPAN FINSET)
    , testHypergraph_ @(SPAN FINSET)
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
  genSome = mapSome SP <$> genSome
  genSomeSmall = mapSome SP <$> genSomeSmall

-- instance (Ob a, Ob b, Testable k, TestObIsOb k) => TestingEqShow (Span a (b :: SPAN k)) where
instance (Ob a, Ob b) => TestingEqShow (Span a (b :: SPAN FINSET)) where
  eqP (Span @c1 l1 r1) (Span @c2 l2 r2) =
    l1 //
      l2 //
        case eqFinSet @c1 @c2 of
          Just Refl -> do
            eql <- eqP l1 l2
            eqr <- eqP r1 r2
            -- Both legs map *out* of the apex, so any relabelling of it is admissible: two spans
            -- are isomorphic exactly when their multisets of (left, right) image pairs agree.
            -- Cospan's legs map in, which is why it has to search instead -- see "Props.Cospan".
            let hasIso = sort (zip (toList (unFinSet l1)) (toList (unFinSet r1))) == sort (zip (toList (unFinSet l2)) (toList (unFinSet r2)))
            pure $ (eql && eqr) || hasIso
          Nothing -> pure False
  showP (Span @c l r) = "Span @(" ++ showOb @_ @c ++ ") (" ++ showP l ++ ") (" ++ showP r ++ ")" \\ l

-- instance (TestOb a, TestOb b, Testable k, TestObIsOb k) => TestableType (Span a (b :: SPAN k)) where
instance (TestOb a, TestOb b) => TestableType (Span a (b :: SPAN FINSET)) where
  gen = GenNonEmpty loop
    where
      loop = do
        Some @c <- genSome @_
        case (gen @(c ~> UN SP a), gen @(c ~> UN SP b)) of
          (GenEmpty _, _) -> loop
          (_, GenEmpty _) -> loop
          (GenNonEmpty l, GenNonEmpty r) -> Span <$> l <*> r
instance TestableProfunctor (Span :: CAT (SPAN FINSET))
