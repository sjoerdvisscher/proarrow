{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.FinSet where

import Data.Fin (Fin, absurd, universe)
import Data.Proxy (Proxy (..))
import Data.Type.Equality (TestEquality (..), type (:~:) (..))
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3, Nat4, SNat (..), SNatI, reflect, snat)
import Data.Vec.Lazy (Vec (..), repeat)
import Test.Tasty (TestTree, testGroup)
import Prelude qualified as P

import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Core (CategoryOf (..), UN)

import Proarrow.Testing
  ( GenTotal (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , invmap
  , oneElem
  , optGen
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws

test :: TestTree
test =
  testGroup
    "FinSet"
    [ propCategory @FINSET
    , propTerminalObject @FINSET
    , propInitialObject @FINSET
    , propBinaryProducts_ @FINSET
    , propCartesian_ @FINSET
    , propMonoidal_ @FINSET
    , propMonoidalHom_ @FINSET
    , propSymMonoidal_ @FINSET
    , propCopyDiscard_ @FINSET
    , propBinaryCoproducts_ @FINSET
    , propDistributive_ @FINSET
    , propClosed_ @FINSET
    , propEqualizers_ @FINSET
    , propCoequalizers_ @FINSET
    , propPullbacks_ @FINSET
    , propPushouts_ @FINSET
    , testComonoid_ @(FS Nat0)
    , testComonoid_ @(FS Nat1)
    , testComonoid_ @(FS Nat2)
    , testComonoid_ @(FS Nat3)
    , testMonoid_ @(FS Nat1)
    ]

-- | Two finite sets are the same object when they have the same cardinality. Not a method of
-- 'Testable': no law needs to compare objects (see "Props.Span"\'s 'eqP' for why the ones that do
-- are comparing something existential).
eqFinSet :: forall (a :: FINSET) (b :: FINSET). (Ob a, Ob b) => P.Maybe (a :~: b)
eqFinSet = (\Refl -> Refl) P.<$> testEquality (snat @(UN FS a)) (snat @(UN FS b))

instance Testable FINSET where
  type TestOb a = Ob a
  showOb @(FS a) = P.show (reflect (Proxy @a))
  genSome = genSomeDef @'[FS Nat1, FS Nat2, FS Nat3, FS Nat4]

instance (Ob a, Ob b) => TestingEqShow (FinSet a b)
instance (Ob a, Ob b) => TestableType (FinSet a b) where
  gen = invmap FinSet unFinSet gen
instance TestableProfunctor FinSet

instance (P.Eq a, P.Show a) => TestingEqShow (Vec n a)
instance (P.Eq a, P.Show a, TestableType a, SNatI n) => TestableType (Vec n a) where
  gen = case gen of
    GenEmpty absrd -> case snat @n of
      SZ -> oneElem VNil
      SS -> GenEmpty \(a ::: _) -> absrd a
    GenNonEmpty g -> GenNonEmpty (P.sequence (repeat @n g))

instance (SNatI n) => TestingEqShow (Fin n)
instance (SNatI n) => TestableType (Fin n) where
  gen = case snat @n of
    SZ -> GenEmpty absurd
    SS -> optGen universe
