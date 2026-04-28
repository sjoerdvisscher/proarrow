{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Cospan where

import Data.Foldable (toList)
import Data.Maybe (isJust)
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3)
import Data.Typeable ((:~:) (..))
import Test.Tasty (TestTree, testGroup)
import Prelude (Bool (..), Maybe (..), pure, zip, ($), (&&), (++), (<$>), (<*>), (||))

import Proarrow.Category.Instance.Cospan (COSPAN (..), Cospan (..))
import Proarrow.Category.Instance.FinSet (FINSET (..), findIso, unFinSet)
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

test :: TestTree
test =
  testGroup
    "Cospan(FinSet)"
    [ propCategory @(COSPAN FINSET)
    , propMonoidal_ @(COSPAN FINSET)
    , propSymMonoidal_ @(COSPAN FINSET)
    , propClosed_ @(COSPAN FINSET)
    , propStarAutonomous_ @(COSPAN FINSET)
    , testMonoid_ @(CS (FS Nat0))
    , testMonoid_ @(CS (FS Nat1))
    , testMonoid_ @(CS (FS Nat2))
    , testMonoid_ @(CS (FS Nat3))
    , testComonoid_ @(CS (FS Nat0))
    , testComonoid_ @(CS (FS Nat1))
    , testComonoid_ @(CS (FS Nat2))
    , testComonoid_ @(CS (FS Nat3))
    ]

-- instance (Testable k, HasPushouts k, TestObIsOb k) => Testable (COSPAN k) where
instance Testable (COSPAN FINSET) where
  type TestOb a = Ob a
  showOb @a = showOb @_ @(UN CS a)
  eqOb @a @b = (\Refl -> Refl) <$> eqOb @_ @(UN CS a) @(UN CS b)
  genSome = mapSome CS <$> genSome

-- instance (Ob a, Ob b, Testable k, TestObIsOb k) => TestingEqShow (Cospan a (b :: COSPAN k)) where
instance (Ob a, Ob b) => TestingEqShow (Cospan a (b :: COSPAN FINSET)) where
  eqP (Cospan @c1 l1 r1) (Cospan @c2 l2 r2) =
    l1 //
      l2 //
        case eqOb @_ @c1 @c2 of
          Just Refl -> do
            eql <- eqP l1 l2
            eqr <- eqP r1 r2
            let hasIso =
                  isJust
                    ( findIso @(UN FS c1)
                        (zip (toList (unFinSet l1)) (toList (unFinSet l2)) ++ zip (toList (unFinSet r1)) (toList (unFinSet r2)))
                    )
            pure $ (eql && eqr) || hasIso
          Nothing -> pure False
  showP (Cospan @c l r) = "Cospan @(" ++ showOb @_ @c ++ ") (" ++ showP l ++ ") (" ++ showP r ++ ")" \\ l

-- instance (TestOb a, TestOb b, Testable k, TestObIsOb k) => TestableType (Cospan a (b :: COSPAN k)) where
instance (TestOb a, TestOb b) => TestableType (Cospan a (b :: COSPAN FINSET)) where
  gen = GenNonEmpty $ loop
    where
      loop = do
        Some @c <- genSome @_
        case (gen @(UN CS a ~> c), gen @(UN CS b ~> c)) of
          (GenEmpty _, _) -> loop
          (_, GenEmpty _) -> loop
          (GenNonEmpty l, GenNonEmpty r) -> Cospan <$> l <*> r
