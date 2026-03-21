{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Simplex where

import Data.Fin (Fin (..), absurd, isMin)
import Data.Foldable (Foldable (..), toList)
import Data.Monoid (All (..), Ap (..))
import Data.Vec.Lazy (Vec (..), universe, zipWith)
import Data.Void qualified as Void
import Test.Falsify.Generator (Function (..), choose, functionMap)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (fst, id, snd, zipWith)

import Proarrow.Category.Instance.Simplex (Forget, IsNat (..), Nat (..), Pick, SNat (..), Simplex (..))
import Proarrow.Core (Ob)

import Proarrow.Profunctor.Representable (Rep)
import Props
import Props.Hask ()
import Testable
  ( GenTotal (..)
  , ShowP (..)
  , Testable (..)
  , TestableType (..)
  , TestingEqShow (..)
  , genObDef
  , one
  , optGen
  , pattern GenNonEmpty
  )

test :: TestTree
test =
  testGroup
    "Simplex"
    [ propCategory @Nat
    , propInitialObject @Nat
    , propTerminalObject @Nat
    , propMonoidal_ @Nat
    , testMonoid_ @Z
    , testMonoid_ @(S Z)
    , testProfunctor @(Rep Forget)
    , testProfunctor @(Rep (Pick Bool))
    ]

instance Testable Nat where
  type TestOb a = Ob a
  genOb = genObDef @'[Z, S Z, S (S Z), S (S (S Z))]
  showOb @a = show (singNat @a)

instance (Ob a, Ob b) => TestingEqShow (Simplex a b)
instance (Ob a, Ob b) => TestableType (Simplex a b) where
  gen = case (singNat @a, singNat @b) of
    (SZ, SZ) -> one ZZ
    (SZ, SS @b') -> case gen @(Simplex Z b') of
      GenEmpty f -> GenEmpty (\(Y p) -> f p)
      GenNonEmpty gf -> GenNonEmpty (Y <$> gf)
    (SS, SZ) -> GenEmpty \case {}
    (SS @a', SS @b') -> case (gen @(Simplex a' b), gen @(Simplex (S a') b')) of
      (GenEmpty l, GenEmpty r) -> GenEmpty \case
        X f -> l f
        Y f -> r f
      (GenNonEmpty gf, GenEmpty _) -> GenNonEmpty (X <$> gf)
      (GenEmpty _, GenNonEmpty gg) -> GenNonEmpty (Y <$> gg)
      (GenNonEmpty gf, GenNonEmpty gg) -> GenNonEmpty (choose (X <$> gf) (Y <$> gg))

instance (IsNat n) => TestingEqShow (Fin n)
instance (IsNat n) => TestableType (Fin n) where
  gen = case singNat @n of
    SZ -> GenEmpty absurd
    _ -> optGen (toList universe)

instance (IsNat n) => Function (Fin n) where
  function = case singNat @n of
    SZ -> fmap (functionMap absurd Void.absurd) . function @Void.Void
    SS @m -> fmap (functionMap isMin (maybe FZ FS)) . function @(Maybe (Fin m))

instance (TestableType a, IsNat n) => TestableType (Vec n a) where
  gen = case gen @a of
    GenEmpty ax -> case universe @n of VNil -> one VNil; _ -> GenEmpty \(a ::: _) -> ax a
    GenNonEmpty ga -> GenNonEmpty (traverse (\_ -> ga) universe)
instance (TestingEqShow a, IsNat n) => TestingEqShow (Vec n a) where
  eqP VNil VNil = pure True
  eqP as bs = getAll <$> getAp (fold (zipWith (\l r -> Ap (fmap All (eqP l r))) as bs))
  showP = show . fmap ShowP

instance (IsNat n, Function a) => Function (Vec n a) where
  function = case singNat @n of
    SZ -> fmap (functionMap (\VNil -> ()) (\() -> VNil)) . function @()
    SS @m -> fmap (functionMap (\(x ::: xs) -> (x, xs)) (\(x, xs) -> (x ::: xs))) . function @(a, Vec m a)