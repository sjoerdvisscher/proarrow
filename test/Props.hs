{-# LANGUAGE AllowAmbiguousTypes #-}

module Props where

import Control.Applicative (Const (..))
import Control.Monad (when)
import Data.Data (Proxy (..), (:~:) (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Kind (Constraint)
import Data.List (nub)
import Data.Monoid qualified as P
import GHC.Exts qualified as GHC
import GHC.TypeLits (KnownSymbol, sameSymbol)
import Test.Tasty (TestTree)
import Test.Tasty.Falsify (Property, testFailed, testProperty)
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Category.Instance.Ap (A, AP, Ap (..))
import Proarrow.Category.Instance.Free (All, FREE (..), Lower, Show2, emb, fold)
import Proarrow.Core (CategoryOf (..), Is, Obj, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Object.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Object.BinaryProduct qualified as BinaryProduct
import Proarrow.Object.Initial qualified as Initial
import Proarrow.Object.Terminal qualified as Terminal
import Proarrow.Profunctor.Representable (FunctorForRep (..), Rep)
import Proarrow.Tools.Laws (AssertEq (..), Elem (..), Laws (..), Place (..), Sym (..), Var)
import Proarrow.Tools.Laws qualified as Cat

import Testable (Some (..), TestObIsOb, Testable (..), TestableProfunctor (..))

type family Reqs (tys :: [FREE cs (Var cs)]) (lut :: [(GHC.Symbol, k)]) :: GHC.Constraint where
  Reqs '[] lut = ()
  Reqs (ty ': tys) (lut :: [(GHC.Symbol, k)]) =
    (Is A (Lower (Rep (Lookup lut)) ty), TestOb (UN A (Lower (Rep (Lookup lut)) ty)), Reqs tys lut)

type family AssocLookup (lut :: [(GHC.Symbol, k)]) (a :: GHC.Symbol) :: k where
  AssocLookup '[ '(s, k)] a = k
  AssocLookup ('(s, k) ': lut) s = k
  AssocLookup ('(s, k) ': lut) a = AssocLookup lut a

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
  :: forall {k} cs (lut :: [(GHC.Symbol, k)])
   . ( All cs k
     , All cs (FREE cs (Var cs))
     , All cs (AP PropData k)
     , Laws cs
     , Testable k
     , Typeable cs
     , Reqs (EqTypes cs) lut
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
                    (Const [show (emb @_ @_ @cs p) ++ " = " ++ showP v])
                )
        )
        g
        \\ g
    go :: AssertEq cs -> Property ()
    go ((:=:) @a @b l r) = do
      elem2testOb @a @(EqTypes cs) @lut $
        elem2testOb @b @(EqTypes cs) @lut $ do
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
                ++ showP fl
                ++ "\nRHS = "
                ++ showP fr

propCategory
  :: forall k
   . (Testable k, CategoryOf k)
  => TestTree
propCategory = testProperty "Category" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  Some @d <- genOb
  f <- genP @_ @a @b
  g <- genP @_ @b @c
  h <- genP @_ @c @d
  props @'[] @'[ '("A", a), '("B", b), '("C", c), '("D", d)]
    \case Cat.F -> Wrap f; Cat.G -> Wrap g; Cat.H -> Wrap h

propTerminalObject
  :: forall k
   . (Testable k, Terminal.HasTerminalObject k, TestOb (Terminal.TerminalObject :: k))
  => TestTree
propTerminalObject = testProperty "Terminal object" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genP @_ @a @b
  props @'[Terminal.HasTerminalObject]
    @'[ '("A", a), '("B", b)]
    \case Terminal.F -> Wrap f

propInitialObject
  :: forall k
   . (Testable k, Initial.HasInitialObject k, TestOb (Initial.InitialObject :: k))
  => TestTree
propInitialObject = testProperty "Initial object" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genP @_ @a @b
  props @'[Initial.HasInitialObject]
    @'[ '("A", a), '("B", b)]
    \case Initial.F -> Wrap f

propBinaryProducts
  :: forall k
   . (Testable k, BinaryProduct.HasBinaryProducts k)
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a BinaryProduct.&& b)) => r) -> r)
  -> TestTree
propBinaryProducts withTestObProd = testProperty "Binary products" $ do
  Some @a <- genOb
  Some @b <- genOb
  Some @c <- genOb
  Some @z <- genOb
  f <- genP @_ @a @b
  g <- genP @_ @a @c
  h <- genP @_ @z @a
  withTestObProd @b @c $ props @'[BinaryProduct.HasBinaryProducts]
    @'[ '("A", a), '("B", b), '("C", c), '("Z", z)]
    \case BinaryProduct.F -> Wrap f; BinaryProduct.G -> Wrap g; BinaryProduct.H -> Wrap h

propBinaryProducts_
  :: forall k
   . (Testable k, BinaryProduct.HasBinaryProducts k, TestObIsOb k)
  => TestTree
propBinaryProducts_ = propBinaryProducts @k (\ @a @b r -> BinaryProduct.withObProd @k @a @b r)

propBinaryCoproducts
  :: forall k
   . (Testable k, BinaryCoproduct.HasBinaryCoproducts k)
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a BinaryCoproduct.|| b)) => r) -> r)
  -> TestTree
propBinaryCoproducts withTestObCoprod = testProperty "Binary coproducts" $ do
  Some @a <- genOb
  Some @b <- genOb
  Some @c <- genOb
  Some @z <- genOb
  f <- genP @_ @a @c
  g <- genP @_ @b @c
  h <- genP @_ @c @z
  withTestObCoprod @a @b $ props @'[BinaryCoproduct.HasBinaryCoproducts]
    @'[ '("A", a), '("B", b), '("C", c), '("Z", z)]
    \case BinaryCoproduct.F -> Wrap f; BinaryCoproduct.G -> Wrap g; BinaryCoproduct.H -> Wrap h

propBinaryCoproducts_
  :: forall k
   . (Testable k, BinaryCoproduct.HasBinaryCoproducts k, TestObIsOb k)
  => TestTree
propBinaryCoproducts_ = propBinaryCoproducts @k (\ @a @b r -> BinaryCoproduct.withObCoprod @k @a @b r)