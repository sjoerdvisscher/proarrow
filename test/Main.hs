{-# LANGUAGE OverloadedLists, GeneralizedNewtypeDeriving, AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import GHC.Generics (Generic)
import Prelude hiding (id, (.))
import Test.Tasty
import Test.Tasty.Falsify
import Test.Falsify.Generator qualified as Gen
import Test.Falsify.Predicate

import Proarrow.Core (CategoryOf(..), Profunctor (..), Promonad (..), Category, CAT)
import qualified GHC.Exts as GHC
import Proarrow.Category.Instance.Free (Laws(..), AllOb, Eq2, Show2, Ok, Lookup (..), AssertEqs (..), Var(..), fold)
import Proarrow.Profunctor.Representable (Representable(..))
import Test.Falsify.GenDefault (GenDefault (..), ViaGeneric (..))
import Test.Falsify.GenDefault.Std (Std)
import Data.Data (Proxy(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts)

instance (Gen.Function a, GenDefault tag b) => GenDefault tag (a -> b) where
  genDefault tag = Gen.applyFun <$> Gen.fun (genDefault tag)

def :: (Show a, GenDefault Std a) => Property a
def = gen (genDefault (Proxy @Std))

data Three = A | B | C deriving (Show, Eq, Generic, Gen.Function)

deriving via ViaGeneric tag Three instance GenDefault tag Three

newtype SimpleP a b = SimpleP (a -> b)
  deriving newtype (GenDefault tag)

deriving instance (Show (a -> b)) => Show (SimpleP a b)

instance Profunctor SimpleP where
  dimap f g (SimpleP h) = SimpleP (g . h . f)

instance Eq (SimpleP Three Three) where
  SimpleP f == SimpleP g = all @[] (\x -> f x == g x) [A, B, C]

instance Show a => Show (Three -> a) where
  show f = show [f x | x <- [A, B, C]]

instance Show a => Show (Bool -> a) where
  show f = show [f x | x <- [False, True]]

genThree :: Gen Three
genThree = Gen.elem [A, B, C]

genThreeToThree :: Gen (Three -> Three)
genThreeToThree = Gen.applyFun <$> Gen.fun genThree

genSimpleP :: Gen (SimpleP Three Three)
genSimpleP = SimpleP <$> genThreeToThree

prop_dimap_id :: Property ()
prop_dimap_id = do
  p <- gen genSimpleP
  assert $ eq .$ ("lhs", dimap id id p)
              .$ ("rhs", p)

prop_dimap_comp :: Property ()
prop_dimap_comp = do
  f <- def @(Three -> Three)
  g <- def @(Three -> Three)
  h <- def @(Three -> Three)
  i <- def @(Three -> Three)
  p <- def @(SimpleP Three Three)
  assert $ eq .$ ("lhs", dimap (f . g) (h . i) p)
              .$ ("rhs", (dimap g h . dimap f i) p)

prop_hask_binary_products :: Property ()
prop_hask_binary_products = do
  f <- def @(Bool -> Bool)
  g <- def @(Bool -> Three)
  props @HasBinaryProducts
    @'[ '("A", Bool), '("B", Bool), '("C", Three)]
    \case { F -> f; G -> g }

props
  :: forall {k} c (lut :: [(GHC.Symbol, k)]) (cat :: CAT k)
   . (c k, Laws c, Ok c (Var c) k, Category cat, AllOb lut)
  => (forall x y. Var c x y -> Lookup lut % x ~> Lookup lut % y) -> Property ()
props pn = go laws where
  go :: AssertEqs c k -> Property ()
  go NoLaws = pure ()
  go (reqs1 :>>: reqs2) = go reqs1 >> go reqs2
  go ((:=:) k) = k @_ @lut \l r -> do
    let f g = fold @'[c] (Lookup @lut . pn) g \\ g
    assert $ eq .$ ("lhs", f l) .$ ("rhs", f r)



main :: IO ()
main = defaultMain $ testGroup "Profunctor Laws"
  [ testProperty "dimap id id = id" prop_dimap_id
  , testProperty "dimap composition" prop_dimap_comp
  ]