{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Control.Applicative (Const (..))
import Control.Monad (when)
import Data.Data (Proxy (..), (:~:) (..))
import Data.Functor.Product (Product (..))
import Data.Kind (Constraint, Type)
import Data.List (intercalate, nub)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Monoid qualified as P
import GHC.Exts qualified as GHC
import Test.Falsify.GenDefault (GenDefault (..))
import Test.Falsify.GenDefault.Std (Std)
import Test.Falsify.Generator qualified as Gen
import Test.Tasty
import Test.Tasty.Falsify
import Type.Reflection (Typeable, typeRep)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Data.Functor.Identity (Identity (..))
import GHC.TypeLits (KnownSymbol, sameSymbol)
import Proarrow.Category.Instance.Ap (A, AP, Ap (..))
import Proarrow.Category.Instance.Free (All, FREE (..), Free (..), Lower, Show2, TermF, emb, fold, type (*!))
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Object (Ob', Obj)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (FunctorForRep (..), Rep)
import Unsafe.Coerce (unsafeCoerce)

type AllTest :: forall {j} {k}. (Type -> Constraint) -> j +-> k -> Constraint
class (forall a b. (TestOb a, TestOb b) => c (p a b)) => AllTest c p
instance (forall a b. (TestOb a, TestOb b) => c (p a b)) => AllTest c p

type TestableProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Testable j, Testable k, Profunctor p, AllTest Show p) => TestableProfunctor (p :: j +-> k) where
  genP :: (TestOb (a :: k), TestOb (b :: j)) => Property (p a b)
  eqP :: (TestOb (a :: k), TestOb (b :: j)) => p a b -> p a b -> Property Bool

class (Typeable k, forall (a :: k). (TestOb a) => Ob' a, TestableProfunctor ((~>) :: CAT k)) => Testable k where
  type TestOb (a :: k) :: GHC.Constraint
  showOb :: forall (a :: k) -> (TestOb a) => String

instance Testable Type where
  type TestOb (a :: Type) = (Typeable a, Eq a, Show a, GenDefault Std a, Gen.Function a, Enum a, Bounded a)
  showOb a = show (typeRep @a)
instance (Enum a, Enum b, Bounded b) => Enum (a, b) where
  toEnum n = (toEnum (n `div` lenB), toEnum (n `mod` lenB))
    where
      lenB = fromEnum (maxBound :: b) + 1
  fromEnum (a, b) = fromEnum a * lenB + fromEnum b
    where
      lenB = fromEnum (maxBound :: b) + 1
instance (Enum a) => Enum (Maybe a) where
  toEnum 0 = Nothing
  toEnum n = Just (toEnum (n - 1))
  fromEnum Nothing = 0
  fromEnum (Just x) = 1 + fromEnum x
instance (Bounded a) => Bounded (Maybe a) where
  minBound = Nothing
  maxBound = Just maxBound
instance (TestOb a, TestOb b) => Show (a -> b) where
  show f = intercalate "," [show x ++ "->" ++ show (f x) | x <- [minBound .. maxBound]]
instance TestableProfunctor (->) where
  genP = def
  eqP l r = do
    a <- def
    pure $ l a == r a

instance (Gen.Function a, GenDefault tag b) => GenDefault tag (a -> b) where
  genDefault tag = Gen.applyFun <$> Gen.fun (genDefault tag)

def :: (Show a, GenDefault Std a) => Property a
def = gen (genDefault (Proxy @Std))

propHaskTerminalObject :: Property ()
propHaskTerminalObject = propTerminalObject @[Bool, (Bool, Bool), Maybe Bool]

propHaskBinaryProducts :: Property ()
propHaskBinaryProducts = propBinaryProducts @[Bool, (Bool, Bool), Maybe Bool] (\r -> r)

data Some k where
  Some :: forall {k} a. (TestOb (a :: k)) => Some k

class MkSomeList (as :: [k]) where
  mkSomeList :: [Some k]
instance MkSomeList '[] where
  mkSomeList = []
instance (TestOb (a :: k), MkSomeList as) => MkSomeList (a ': as) where
  mkSomeList = Some @a : mkSomeList @k @as
instance (Testable k) => Show (Some k) where
  show (Some @a) = showOb a

elem :: (Show a) => [a] -> Property a
elem [] = discard
elem (x : xs) = gen (Gen.elem (x :| xs))

propTerminalObject
  :: forall {k} (obs :: [k])
   . (TestableProfunctor ((~>) :: CAT k), Typeable k, HasTerminalObject k, TestOb (TerminalObject :: k), MkSomeList obs)
  => Property ()
propTerminalObject = do
  let obs = mkSomeList @k @obs
  Some @a <- elem obs
  Some @b <- elem obs
  f <- genP @_ @a @b
  props @'[HasTerminalObject]
    @'[ '("A", a), '("B", b)]
    \case T -> Wrap f

propBinaryProducts
  :: forall {k} (obs :: [k])
   . (TestableProfunctor ((~>) :: CAT k), Typeable k, HasBinaryProducts k, MkSomeList obs)
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a && b)) => r) -> r) -> Property ()
propBinaryProducts withTestObProd = do
  let obs = mkSomeList @k @obs
  Some @a <- elem obs
  Some @b <- elem obs
  Some @c <- elem obs
  Some @z <- elem obs
  f <- genP @_ @a @b
  g <- genP @_ @a @c
  h <- genP @_ @z @a
  withTestObProd @b @c $ props @'[HasBinaryProducts]
    @'[ '("A", a), '("B", b), '("C", c), '("Z", z)]
    \case F -> Wrap f; G -> Wrap g; H -> Wrap h

type family Reqs (tys :: [FREE cs (Var cs)]) (lut :: [(GHC.Symbol, k)]) :: GHC.Constraint where
  Reqs '[] lut = ()
  Reqs (ty ': tys) (lut :: [(GHC.Symbol, k)]) =
    (Is A (Lower (Rep (Lookup lut)) ty), TestOb (UN A (Lower (Rep (Lookup lut)) ty)), Reqs tys lut)

data Place as a where
  Here :: Place (a ': as) a
  There :: (b `Elem` as) => Place (a ': as) b

type Elem :: forall {a}. a -> [a] -> Constraint
class c `Elem` cs where
  place :: Place cs c
instance {-# OVERLAPPABLE #-} (c `Elem` cs) => c `Elem` (d ': cs) where
  place = There
instance c `Elem` (c ': cs) where
  place = Here

infix 0 :=:
type AssertEq :: [Kind -> Constraint] -> [FREE cs (Var cs)] -> Type
data AssertEq cs tys where
  (:=:)
    :: forall {cs} {tys} (a :: FREE cs (Var cs)) (b :: FREE cs (Var cs))
     . (a `Elem` tys, b `Elem` tys) => Free a b -> Free a b -> AssertEq cs tys
deriving instance (Show2 (Var cs)) => Show (AssertEq cs tys)

data family Var (cs :: [Kind -> Constraint]) (a :: GHC.Symbol) (b :: GHC.Symbol)
class Laws (cs :: [Kind -> Constraint]) (tys :: [FREE cs (Var cs)]) | cs -> tys where
  laws :: [AssertEq cs tys]

type family AssocLookup (lut :: [(GHC.Symbol, k)]) (a :: GHC.Symbol) :: k where
  AssocLookup '[ '(s, k)] a = k
  AssocLookup ('(s, k) ': lut) s = k
  AssocLookup ('(s, k) ': lut) a = AssocLookup lut a

data Sym a b where
  Sym :: (KnownSymbol a, KnownSymbol b) => a :~: b -> Sym a b
instance Profunctor (Sym :: CAT GHC.Symbol) where
  dimap = dimapDefault
  r \\ Sym{} = r
instance Promonad (Sym :: CAT GHC.Symbol) where
  id = Sym Refl
  Sym Refl . Sym Refl = Sym Refl
instance CategoryOf GHC.Symbol where
  type (~>) = Sym
  type Ob a = (KnownSymbol a)

data instance Var '[HasTerminalObject] a b where
  T :: Var '[HasTerminalObject] "A" "B"
deriving instance Show (Var '[HasTerminalObject] a b)
instance Laws '[HasTerminalObject] '[EMB "A", TermF] where
  laws = [terminate . emb T :=: terminate]

data instance Var '[HasBinaryProducts] a b where
  F :: Var '[HasBinaryProducts] "A" "B"
  G :: Var '[HasBinaryProducts] "A" "C"
  H :: Var '[HasBinaryProducts] "Z" "A"
deriving instance Show (Var '[HasBinaryProducts] a b)
instance Laws '[HasBinaryProducts] [EMB "A", EMB "B", EMB "C", EMB "Z", EMB "B" *! EMB "C"] where
  laws =
    let f = emb F; g = emb G; h = emb H
    in [ fst . (f &&& g) :=: f
       , snd . (f &&& g) :=: g
       , (f . h) &&& (g . h) :=: (f &&& g) . h
       ]

type PropData = Product Identity (Const [String])

elem2testOb
  :: forall a tys lut r
   . (Elem a tys, Reqs tys lut)
  => ((Is A (Lower (Rep (Lookup lut)) a), TestOb (UN A (Lower (Rep (Lookup lut)) a))) => r) -> r
elem2testOb r = case place @a @tys of
  Here -> r
  There @_ @as -> elem2testOb @a @as @lut r

type AllOb :: forall {k}. [(GHC.Symbol, k)] -> Constraint
class AllOb (lut :: [(GHC.Symbol, k)]) where
  lookupId :: forall (t :: GHC.Symbol). (KnownSymbol t) => Obj (AssocLookup lut t)
instance (TestOb a, Ob a, CategoryOf k) => AllOb '[ '(s, a :: k)] where
  lookupId = id
instance (TestOb a, Ob (a :: k), KnownSymbol s, CategoryOf k, AllOb ('(s', b) ': lut)) => AllOb ('(s, a) ': '(s', b) ': lut) where
  lookupId @t = case sameSymbol (Proxy @s) (Proxy @t) of
    Just Refl -> id
    -- Is there a way to avoid unsafeCoerce here? Could decideSymbol help? GHC needs to know that t does *not* equal s.
    Nothing -> unsafeCoerce (lookupId @('(s', b) ': lut) @t)

data family Lookup (lut :: [(GHC.Symbol, k)]) :: GHC.Symbol +-> AP PropData k
instance (CategoryOf k, AllOb lut) => FunctorForRep (Lookup lut :: GHC.Symbol +-> AP PropData k) where
  type Lookup lut @ a = A (AssocLookup lut a)
  fmap (Sym @a Refl) = id \\ lookupId @lut @a

data Wrap lut x y where
  Wrap
    :: (TestOb (AssocLookup lut x), TestOb (AssocLookup lut y), KnownSymbol x, KnownSymbol y)
    => (AssocLookup lut x ~> AssocLookup lut y) -> Wrap lut x y
props
  :: forall {k} cs {tys} (lut :: [(GHC.Symbol, k)])
   . ( All cs k
     , All cs (FREE cs (Var cs))
     , All cs (AP PropData k)
     , Laws cs tys
     , Testable k
     , Typeable cs
     , Reqs tys lut
     , AllOb lut
     , Show2 (Var cs)
     )
  => (forall x y. Var cs x y -> Wrap lut x y)
  -> Property ()
props pn = P.getAp (foldMap (P.Ap . go) laws)
  where
    f :: forall (a :: FREE cs (Var cs)) b. a ~> b -> Lower (Rep (Lookup lut)) a ~> Lower (Rep (Lookup lut)) b
    f g =
      fold @cs @(Rep (Lookup lut))
        ( \p -> case pn p of
            Wrap v ->
              Ap
                ( Pair
                    (Identity v)
                    (Const [show (emb @_ @_ @cs p) ++ " = " ++ show v])
                )
        )
        g
        \\ g
    go :: AssertEq cs tys -> Property ()
    go ((:=:) @a @b l r) = do
      elem2testOb @a @tys @lut $
        elem2testOb @b @tys @lut $ do
          let Ap (Pair (Identity fl) (Const vl)) = f l
              Ap (Pair (Identity fr) (Const vr)) = f r
          isEq <- eqP fl fr
          when (not isEq) $
            testFailed $
              "Failed law "
                ++ show l
                ++ " = "
                ++ show r
                ++ ", with: \n"
                ++ unlines (nub (vl ++ vr))
                ++ "LHS = "
                ++ show fl
                ++ "\nRHS = "
                ++ show fr

main :: IO ()
main =
  defaultMain $
    testGroup
      "Hask"
      [ testProperty "Terminal object" propHaskTerminalObject
      , testProperty "Binary products" propHaskBinaryProducts
      ]