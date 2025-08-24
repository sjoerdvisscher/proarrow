{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Data.Data (Proxy (..), Typeable, (:~:) (..))
import Data.Kind (Constraint, Type)
import GHC.Exts qualified as GHC
import GHC.Generics (Generic)
import Test.Falsify.Generator qualified as Gen
import Test.Tasty
import Test.Tasty.Falsify
import Prelude hiding (fst, id, snd, (.), (>>))

import Data.Monoid (Ap (..))
import Proarrow.Category.Instance.Free (Elem (..), FREE (..), Free (..), Lower, Place (..), emb, fold)
import Proarrow.Core (CAT, Category, CategoryOf (..), Kind, Profunctor (..), Promonad (..), dimapDefault, type (+->))
import Proarrow.Object (Ob')
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)
import Test.Falsify.GenDefault (GenDefault (..), ViaGeneric (..))
import Test.Falsify.GenDefault.Std (Std)

class (forall a b. (TestOb a, TestOb b) => c (p a b)) => AllTest c p
instance (forall a b. (TestOb a, TestOb b) => c (p a b)) => AllTest c p
class (Testable j, Testable k, Profunctor p, AllTest Show p) => TestableProfunctor (p :: j +-> k) where
  genP :: (TestOb (a :: k), TestOb (b :: j)) => Property (p a b)
  eqP :: (TestOb (a :: k), TestOb (b :: j)) => p a b -> p a b -> Property ()

class (Typeable k, forall (a :: k). (TestOb a) => Ob' a) => Testable k where
  type TestOb (a :: k) :: GHC.Constraint

instance Testable Type where
  type TestOb (a :: Type) = (Typeable a, Eq a, Show a, GenDefault Std a, Gen.Function a)
instance Show (a -> b) where
  show _ = "<function>"
instance TestableProfunctor (->) where
  genP = def
  eqP l r = do
    a <- def
    if l a == r a
      then pure ()
      else testFailed $ "Expected: " ++ show (r a) ++ ", but got: " ++ show (l a)

instance (Gen.Function a, GenDefault tag b) => GenDefault tag (a -> b) where
  genDefault tag = Gen.applyFun <$> Gen.fun (genDefault tag)

def :: (Show a, GenDefault Std a) => Property a
def = gen (genDefault (Proxy @Std))

data Three = A | B | C deriving (Show, Eq, Generic, Gen.Function)

deriving via ViaGeneric tag Three instance GenDefault tag Three

prop_hask_binary_products :: Property ()
prop_hask_binary_products = do
  f <- def @(Bool -> Bool)
  g <- def @(Bool -> Three)
  propBinaryProducts f g

propBinaryProducts
  :: forall {k} (a :: k) b c
   . (TestableProfunctor ((~>) :: CAT k), Typeable k, HasBinaryProducts k, TestOb a, TestOb b, TestOb c)
  => (a ~> b) -> (a ~> c) -> Property ()
propBinaryProducts f g =
  props @HasBinaryProducts
    @'[ '("A", a), '("B", b), '("C", c)]
    \case F -> f; G -> g

type family Reqs c (tys :: [FREE '[c] (Var c) k]) (lut :: [(GHC.Symbol, k)]) :: GHC.Constraint where
  Reqs c '[] lut = ()
  Reqs c (ty ': tys) (lut :: [(GHC.Symbol, k)]) = (TestOb (Lower (Lookup lut) ty), Reqs c tys lut)

infix 0 :=:
type AssertEq :: (Kind -> Constraint) -> Kind -> [FREE '[c] (Var c) k] -> Type
data AssertEq c k tys where
  (:=:)
    :: forall {k} {c} {tys} (a :: FREE '[c] (Var c) k) (b :: FREE '[c] (Var c) k)
     . (a `Elem` tys, b `Elem` tys) => Free a b -> Free a b -> AssertEq c k tys

data family Var (c :: Kind -> Constraint) (a :: GHC.Symbol) (b :: GHC.Symbol)
class Laws (c :: Kind -> Constraint) (tys :: [FREE '[c] (Var c) k]) | c k -> tys where
  laws :: (c k, Typeable k) => [AssertEq c k tys]

type family AssocLookup (lut :: [(GHC.Symbol, k)]) (a :: GHC.Symbol) :: k where
  AssocLookup '[] a = GHC.Any
  AssocLookup ('(s, k) ': lut) s = k
  AssocLookup ('(s, k) ': lut) a = AssocLookup lut a

type Lookup :: [(GHC.Symbol, k)] -> GHC.Symbol +-> k
data Lookup lut a b where
  Lookup :: forall lut b a. (Ob b) => a ~> Lookup lut % b -> Lookup lut a b
instance (CategoryOf k) => Profunctor (Lookup lut :: GHC.Symbol +-> k) where
  dimap = dimapRep
  r \\ Lookup f = r \\ f
instance (CategoryOf k) => Representable (Lookup lut :: GHC.Symbol +-> k) where
  type Lookup lut % a = AssocLookup lut a
  index (Lookup f) = f
  tabulate f = Lookup f

  -- We can't prove Ob (AssocLookup lut a), since `a` might not occur in `lut`, so we can't implement repMap.
  -- But Lookup is only for use with props, and props doesn't use repMap.
  -- Also the `pn` argument to props proves that all the symbols used in Var are in lut.
  repMap = error "repMap should not be used with Lookup"

instance Profunctor ((:~:) :: CAT GHC.Symbol) where
  dimap = dimapDefault
  r \\ Refl = r
instance Promonad ((:~:) :: CAT GHC.Symbol) where
  id = Refl
  Refl . Refl = Refl
instance CategoryOf GHC.Symbol where
  type (~>) = (:~:)
  type Ob a = ()

data instance Var HasBinaryProducts a b where
  F :: Var HasBinaryProducts "A" "B"
  G :: Var HasBinaryProducts "A" "C"
instance Laws HasBinaryProducts [EMB "A", EMB "B", EMB "C"] where
  laws =
    let f = emb F; g = emb G
    in [ fst . (f &&& g) :=: f
       , snd . (f &&& g) :=: g
       ]

elem2testOb :: forall c a tys lut r. (Elem a tys, Reqs c tys lut) => ((TestOb (Lower (Lookup lut) a)) => r) -> r
elem2testOb r = case place @a @tys of
  Here -> r
  There @_ @as -> elem2testOb @c @a @as @lut r

props
  :: forall {k} c {tys} (lut :: [(GHC.Symbol, k)]) (cat :: CAT k)
   . (c k, Laws c tys, Testable k, Typeable c, Category cat, TestableProfunctor cat, Reqs c tys lut)
  => (forall x y. Var c x y -> Lookup lut % x ~> Lookup lut % y) -> Property ()
props pn = getAp (foldMap (Ap . go) laws)
  where
    go :: AssertEq c k tys -> Property ()
    go ((:=:) @a @b l r) = do
      let f g = fold @'[c] (Lookup @lut . pn) g \\ g
      elem2testOb @c @a @tys @lut $
        elem2testOb @c @b @tys @lut $
          eqP (f l) (f r)

main :: IO ()
main =
  defaultMain $
    testGroup
      "Profunctor Laws"
      [ testProperty "Hask has binary products" prop_hask_binary_products
      ]