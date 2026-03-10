{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Simplex where

import Test.Falsify.Generator (choose)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (fst, id, snd, (.))

import Proarrow.Category.Instance.Simplex (IsNat (..), Nat (..), SNat (..), Simplex (..))
import Proarrow.Core (Ob)

import Props
import Testable (GenTotal (..), Testable (..), TestableType (..), genObDef, one, pattern GenNonEmpty)

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
      GenNonEmpty gf -> GenNonEmpty (Y <$> gf)
    (SS, SZ) -> GenEmpty \case {}
    (SS @a', SS @b') -> case (gen @(Simplex a' b), gen @(Simplex (S a') b')) of
      (GenEmpty l, GenEmpty r) -> GenEmpty \case
        X f -> l f
        Y f -> r f
      (GenNonEmpty gf, GenEmpty _) -> GenNonEmpty (X <$> gf)
      (GenEmpty _, GenNonEmpty gg) -> GenNonEmpty (Y <$> gg)
      (GenNonEmpty gf, GenNonEmpty gg) -> GenNonEmpty (choose (X <$> gf) (Y <$> gg))
