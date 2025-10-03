{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Simplex where

import Test.Falsify.Generator (choose)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (fst, id, snd, (.))

import Proarrow.Category.Instance.Simplex (IsNat (..), Nat (..), SNat (..), Simplex (..))
import Proarrow.Core (Ob)

import Props
import Testable (GenTotal (..), Testable (..), TestableType (..), genObDef, one)

test :: TestTree
test =
  testGroup
    "Simplex"
    [ propCategory @Nat
    , propInitialObject @Nat
    , propTerminalObject @Nat
    , propMonoidal_ @Nat
    , propMonoid_ @Z
    , propMonoid_ @(S Z)
    ]

instance Testable Nat where
  type TestOb a = Ob a
  genOb = genObDef @'[Z, S Z, S (S Z), S (S (S Z))]
  showOb @a = show (singNat @a)

instance (Ob a, Ob b) => TestableType (Simplex a b) where
  gen = case (singNat @a, singNat @b) of
    (SZ, SZ) -> one ZZ
    (SZ, SS @b') -> case gen @(Simplex Z b') of
      GenEmpty f -> GenEmpty (\(Y p) -> f p)
      GenNonEmpty f gf -> GenNonEmpty (Y f) (Y <$> gf)
    (SS, SZ) -> GenEmpty \case {}
    (SS @a', SS @b') -> case (gen @(Simplex a' b), gen @(Simplex (S a') b')) of
      (GenEmpty l, GenEmpty r) -> GenEmpty \case
        X f -> l f
        Y f -> r f
      (GenNonEmpty f gf, GenEmpty _) -> GenNonEmpty (X f) (X <$> gf)
      (GenEmpty _, GenNonEmpty g gg) -> GenNonEmpty (Y g) (Y <$> gg)
      (GenNonEmpty f gf, GenNonEmpty _ gg) -> GenNonEmpty (X f) (choose (X <$> gf) (Y <$> gg))
