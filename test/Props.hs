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
import GHC.TypeLits (KnownSymbol, Symbol, sameSymbol)
import Test.Tasty (TestTree)
import Test.Tasty.Falsify (Property, testFailed, testProperty)
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Category.Instance.Ap (A, AP, Ap (..))
import Proarrow.Category.Instance.Free (All, FREE (..), Lower, Show2, emb, fold)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Object.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Object.BinaryProduct qualified as BinaryProduct
import Proarrow.Object.Initial qualified as Initial
import Proarrow.Object.Terminal qualified as Terminal
import Proarrow.Profunctor.Representable (FunctorForRep (..), Rep)
import Proarrow.Tools.Laws (AssertEq (..), Elem (..), Laws (..), Place (..), Sym (..), Var)

import Testable (Some (..), TestObIsOb, Testable (..), TestableProfunctor (..))

type family Reqs (tys :: [FREE cs (Var cs)]) (lut :: [(Symbol, k)]) :: Constraint where
  Reqs '[] lut = ()
  Reqs (ty ': tys) (lut :: [(Symbol, k)]) =
    (Is A (Lower (Rep (Lookup lut)) ty), TestOb (UN A (Lower (Rep (Lookup lut)) ty)), Reqs tys lut)

type family GenObsReqs (names :: [Symbol]) (lut :: [(Symbol, k)]) :: Constraint where
  GenObsReqs '[] lut = ()
  GenObsReqs (n ': ns) lut = (TestOb (AssocLookup lut n), GenObsReqs ns lut)

type family AssocLookup (lut :: [(Symbol, k)]) (a :: Symbol) :: k where
  AssocLookup '[ '(s, a)] u = a
  AssocLookup ('(s, a) ': '(t, b) : lut) s = a
  AssocLookup ('(s, a) ': '(t, b) : lut) v = AssocLookup ('(t, b) : lut) v

type PropData = Product Identity (Const [String])

elem2testOb
  :: forall a tys lut r
   . (Elem a tys, Reqs tys lut)
  => ((Is A (Lower (Rep (Lookup lut)) a), TestOb (UN A (Lower (Rep (Lookup lut)) a))) => r) -> r
elem2testOb r = case place @a @tys of
  Here -> r
  There @_ @as -> elem2testOb @a @as @lut r

type AllOb :: forall {k}. [(Symbol, k)] -> Constraint
class AllOb (lut :: [(Symbol, k)]) where
  lookupId :: forall (t :: Symbol). (KnownSymbol t) => Wrap lut t t
instance (TestOb a, Ob a, CategoryOf k) => AllOb '[ '(s, a :: k)] where
  lookupId = Wrap id
instance (TestOb a, Ob (a :: k), KnownSymbol s, CategoryOf k, AllOb ('(s', b) ': lut)) => AllOb ('(s, a) ': '(s', b) ': lut) where
  lookupId @t = case sameSymbol (Proxy @s) (Proxy @t) of
    Just Refl -> Wrap id
    -- Is there a way to avoid unsafeCoerce here? Could decideSymbol help? GHC needs to know that t does *not* equal s.
    Nothing -> unsafeCoerce (lookupId @('(s', b) ': lut) @t)

data family Lookup (lut :: [(Symbol, k)]) :: Symbol +-> AP PropData k
instance (CategoryOf k, AllOb lut) => FunctorForRep (Lookup lut :: Symbol +-> AP PropData k) where
  type Lookup lut @ a = A (AssocLookup lut a)
  fmap (Sym @a Refl) = case lookupId @lut @a of Wrap f -> id \\ f

data Wrap lut x y where
  Wrap
    :: (TestOb (AssocLookup lut x), TestOb (AssocLookup lut y), KnownSymbol x, KnownSymbol y)
    => (AssocLookup lut x ~> AssocLookup lut y) -> Wrap lut x y

class GenObs (names :: [Symbol]) where
  genObs
    :: forall k r
     . (Testable k)
    => (forall (lut :: [(Symbol, k)]). (AllOb lut, GenObsReqs names lut) => Property r)
    -> Property r
instance GenObs '[s] where
  genObs @k r = do
    Some @a <- genOb @k
    r @'[ '(s, a)]
instance (KnownSymbol s, KnownSymbol t) => GenObs '[s, t] where
  genObs @k r = do
    Some @a <- genOb @k
    Some @b <- genOb @k
    case lookupId @'[ '(s, a), '(t, b)] @t of
      Wrap{} -> r @'[ '(s, a), '(t, b)]
instance (KnownSymbol s, KnownSymbol t, KnownSymbol u) => GenObs '[s, t, u] where
  genObs @k r = do
    Some @a <- genOb @k
    Some @b <- genOb @k
    Some @c <- genOb @k
    case (lookupId @'[ '(s, a), '(t, b), '(u, c)] @t, lookupId @'[ '(s, a), '(t, b), '(u, c)] @u) of
      (Wrap{}, Wrap{}) -> r @'[ '(s, a), '(t, b), '(u, c)]
instance (KnownSymbol s, KnownSymbol t, KnownSymbol u, KnownSymbol v) => GenObs '[s, t, u, v] where
  genObs @k r = do
    Some @a <- genOb @k
    Some @b <- genOb @k
    Some @c <- genOb @k
    Some @d <- genOb @k
    case ( lookupId @'[ '(s, a), '(t, b), '(u, c), '(v, d)] @t
         , lookupId @'[ '(s, a), '(t, b), '(u, c), '(v, d)] @u
         , lookupId @'[ '(s, a), '(t, b), '(u, c), '(v, d)] @v
         ) of
      (Wrap{}, Wrap{}, Wrap{}) -> r @'[ '(s, a), '(t, b), '(u, c), '(v, d)]

props
  :: forall {k} cs (lut :: [(Symbol, k)])
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

-- Can't use @Laws@ here, because the free category automatically satisfy these laws.
propCategory
  :: forall k
   . (Testable k, CategoryOf k)
  => TestTree
propCategory = testProperty "Category" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genP @((~>) :: CAT k) @a @b
  isEqIdL <- eqP (id . f) f
  when (not isEqIdL) $
    testFailed $
      "Failed left identity: \n"
        ++ "id . f = "
        ++ showP (id . f)
        ++ "\nf = "
        ++ showP f
  isEqIdR <- eqP (f . id) f
  when (not isEqIdR) $
    testFailed $
      "Failed right identity: \n"
        ++ "f . id = "
        ++ showP (f . id)
        ++ "\nf = "
        ++ showP f
  Some @c <- genOb
  Some @d <- genOb
  g <- genP @_ @b @c
  h <- genP @_ @c @d
  isEq <- eqP ((h . g) . f) (h . (g . f))
  when (not isEq) $
    testFailed $
      "Failed associativity: \n"
        ++ "(h . g) . f = "
        ++ showP ((h . g) . f)
        ++ "\nh . (g . f) = "
        ++ showP (h . (g . f))

propTerminalObject
  :: forall k
   . (Testable k, Terminal.HasTerminalObject k, TestOb (Terminal.TerminalObject :: k))
  => TestTree
propTerminalObject = testProperty "Terminal object" $
  genObs @'["A", "B"] @k \ @lut -> do
    f <- genP
    props @'[Terminal.HasTerminalObject] @lut
      \case Terminal.F -> Wrap f

propInitialObject
  :: forall k
   . (Testable k, Initial.HasInitialObject k, TestOb (Initial.InitialObject :: k))
  => TestTree
propInitialObject = testProperty "Initial object" $
  genObs @'["A", "B"] @k \ @lut -> do
    f <- genP
    props @'[Initial.HasInitialObject] @lut
      \case Initial.F -> Wrap f

propBinaryProducts
  :: forall k
   . (Testable k, BinaryProduct.HasBinaryProducts k)
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a BinaryProduct.&& b)) => r) -> r)
  -> TestTree
propBinaryProducts withTestObProd = testProperty "Binary products" $
  genObs @'["A", "B", "C", "Z"] \ @lut -> do
    f <- genP
    g <- genP
    h <- genP
    withTestObProd @(AssocLookup lut "B") @(AssocLookup lut "C") $
      props @'[BinaryProduct.HasBinaryProducts] @lut
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
propBinaryCoproducts withTestObCoprod = testProperty "Binary coproducts" $
  genObs @'["A", "B", "C", "Z"] \ @lut -> do
    f <- genP
    g <- genP
    h <- genP
    withTestObCoprod @(AssocLookup lut "A") @(AssocLookup lut "B") $
      props @'[BinaryCoproduct.HasBinaryCoproducts] @lut
        \case BinaryCoproduct.F -> Wrap f; BinaryCoproduct.G -> Wrap g; BinaryCoproduct.H -> Wrap h

propBinaryCoproducts_
  :: forall k
   . (Testable k, BinaryCoproduct.HasBinaryCoproducts k, TestObIsOb k)
  => TestTree
propBinaryCoproducts_ = propBinaryCoproducts @k (\ @a @b r -> BinaryCoproduct.withObCoprod @k @a @b r)