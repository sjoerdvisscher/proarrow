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
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, lmap, obj, rmap, type (+->))
import Proarrow.Object.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Object.BinaryProduct qualified as BinaryProduct
import Proarrow.Object.Initial qualified as Initial
import Proarrow.Object.Terminal qualified as Terminal
import Proarrow.Profunctor.Representable (FunctorForRep (..), Rep)
import Proarrow.Tools.Laws (AssertEq (..), Elem (..), Laws (..), Place (..), Sym (..), Var)

import Proarrow.Category.Monoidal qualified as Monoidal
import Proarrow.Monoid qualified as Monoid
import Proarrow.Object.Exponential qualified as Exponential
import Testable (Some (..), TestObIsOb, Testable (..), TestableProfunctor, TestableType (..), genP)

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
          case (f l, f r) of
            (Ap (Pair (Identity fl) (Const vl)), Ap (Pair (Identity fr) (Const vr))) -> do
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

genVar
  :: forall {k} (lut :: [(Symbol, k)]) a b
   . (TestableType (AssocLookup lut a ~> AssocLookup lut b))
  => Property (AssocLookup lut a ~> AssocLookup lut b)
genVar = genP

testEq :: (TestableType a) => String -> String -> a -> String -> a -> Property ()
testEq nm sl l sr r = do
  isEq <- eqP l r
  when (not isEq) $
    testFailed $
      "Failed "
        ++ nm
        ++ ":\n"
        ++ sl
        ++ " = "
        ++ showP l
        ++ "\n"
        ++ sr
        ++ " = "
        ++ showP r

-- Can't use @Laws@ here, because the free category automatically satisfy these laws.
propCategory :: forall k. (Testable k) => TestTree
propCategory = testProperty "Category" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genP @(a ~> b)
  testEq "left identity" "id . f" (id . f) "f" f
  testEq "right identity" "f . id" (f . id) "f" f
  Some @c <- genOb
  Some @d <- genOb
  g <- genP @(b ~> c)
  h <- genP @(c ~> d)
  testEq "associativity" "(h . g) . f" ((h . g) . f) "h . (g . f)" (h . (g . f))

propTerminalObject
  :: forall k
   . (Testable k, Terminal.HasTerminalObject k, TestOb (Terminal.TerminalObject :: k))
  => TestTree
propTerminalObject = testProperty "Terminal object" $
  genObs @'["A", "B"] @k \ @lut -> do
    f <- genVar @lut @"A" @"B"
    props @'[Terminal.HasTerminalObject] @lut
      \case Terminal.F -> Wrap f

propInitialObject
  :: forall k
   . (Testable k, Initial.HasInitialObject k, TestOb (Initial.InitialObject :: k))
  => TestTree
propInitialObject = testProperty "Initial object" $
  genObs @'["A", "B"] @k \ @lut -> do
    f <- genVar @lut @"A" @"B"
    props @'[Initial.HasInitialObject] @lut
      \case Initial.F -> Wrap f

propBinaryProducts
  :: forall k
   . (Testable k, BinaryProduct.HasBinaryProducts k)
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a BinaryProduct.&& b)) => r) -> r)
  -> TestTree
propBinaryProducts withTestObProd = testProperty "Binary products" $
  genObs @'["A", "B", "C", "Z"] \ @lut -> do
    f <- genVar @lut @"A" @"B"
    g <- genVar @lut @"A" @"C"
    h <- genVar @lut @"Z" @"A"
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
    f <- genVar @lut @"A" @"C"
    g <- genVar @lut @"B" @"C"
    h <- genVar @lut @"C" @"Z"
    withTestObCoprod @(AssocLookup lut "A") @(AssocLookup lut "B") $
      props @'[BinaryCoproduct.HasBinaryCoproducts] @lut
        \case BinaryCoproduct.F -> Wrap f; BinaryCoproduct.G -> Wrap g; BinaryCoproduct.H -> Wrap h

propBinaryCoproducts_
  :: forall k
   . (Testable k, BinaryCoproduct.HasBinaryCoproducts k, TestObIsOb k)
  => TestTree
propBinaryCoproducts_ = propBinaryCoproducts @k (\ @a @b r -> BinaryCoproduct.withObCoprod @k @a @b r)

propMonoidal
  :: forall k
   . (Testable k, Monoidal.Monoidal k, TestOb (Monoidal.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a Monoidal.** b)) => r) -> r)
  -> TestTree
propMonoidal withTestOb2 = testProperty "Monoidal" $
  genObs @'["A", "B", "C", "D"] \ @lut -> do
    f <- genVar @lut @"A" @"B"
    g <- genVar @lut @"B" @"C"
    h <- genVar @lut @"C" @"D"
    withTestOb2 @(AssocLookup lut "A") @(AssocLookup lut "B")
      $ withTestOb2 @(AssocLookup lut "B") @(AssocLookup lut "C")
      $ withTestOb2 @(AssocLookup lut "C") @(AssocLookup lut "D")
      $ withTestOb2 @Monoidal.Unit @(AssocLookup lut "A")
      $ withTestOb2 @Monoidal.Unit @(AssocLookup lut "B")
      $ withTestOb2 @(AssocLookup lut "A") @Monoidal.Unit
      $ withTestOb2 @(AssocLookup lut "B") @Monoidal.Unit
      $ withTestOb2 @(AssocLookup lut "A" Monoidal.** Monoidal.Unit) @(AssocLookup lut "B")
      $ withTestOb2 @(AssocLookup lut "A" Monoidal.** AssocLookup lut "B") @(AssocLookup lut "C")
      $ withTestOb2 @(AssocLookup lut "A") @(AssocLookup lut "B" Monoidal.** AssocLookup lut "C")
      $ withTestOb2 @(AssocLookup lut "B" Monoidal.** AssocLookup lut "C") @(AssocLookup lut "D")
      $ withTestOb2 @(AssocLookup lut "B") @(AssocLookup lut "C" Monoidal.** AssocLookup lut "D")
      $ withTestOb2 @(AssocLookup lut "A")
        @(AssocLookup lut "B" Monoidal.** (AssocLookup lut "C" Monoidal.** AssocLookup lut "D"))
      $ withTestOb2 @((AssocLookup lut "A" Monoidal.** AssocLookup lut "B") Monoidal.** AssocLookup lut "C")
        @(AssocLookup lut "D")
      $ props @'[Monoidal.Monoidal] @lut
        \case Monoidal.F -> Wrap f; Monoidal.G -> Wrap g; Monoidal.H -> Wrap h

propMonoidal_
  :: forall k
   . (Testable k, Monoidal.Monoidal k, TestOb (Monoidal.Unit @k), TestObIsOb k)
  => TestTree
propMonoidal_ = propMonoidal @k (\ @a @b r -> Monoidal.withOb2 @k @a @b r)

propSymMonoidal
  :: forall k
   . (Testable k, Monoidal.SymMonoidal k, TestOb (Monoidal.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a Monoidal.** b)) => r) -> r)
  -> TestTree
propSymMonoidal withTestOb2 = testProperty "Symmetric monoidal" $
  genObs @'["A", "B", "C"] \ @lut -> do
    withTestOb2 @(AssocLookup lut "A") @(AssocLookup lut "B") $
      withTestOb2 @(AssocLookup lut "C") @(AssocLookup lut "A") $
        withTestOb2 @(AssocLookup lut "A" Monoidal.** AssocLookup lut "B") @(AssocLookup lut "C") $
          withTestOb2 @(AssocLookup lut "B") @(AssocLookup lut "C" Monoidal.** AssocLookup lut "A") $
            props @'[Monoidal.Monoidal, Monoidal.SymMonoidal] @lut \case {}

propSymMonoidal_
  :: forall k
   . (Testable k, Monoidal.SymMonoidal k, TestOb (Monoidal.Unit @k), TestObIsOb k)
  => TestTree
propSymMonoidal_ = propSymMonoidal @k (\ @a @b r -> Monoidal.withOb2 @k @a @b r)

propClosed
  :: forall k
   . (Testable k, Exponential.Closed k, TestOb (Monoidal.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a Monoidal.** b)) => r) -> r)
  -> (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a Exponential.~~> b)) => r) -> r)
  -> TestTree
propClosed withTestOb2 withTestObExp = testProperty "Closed" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  -- TODO: test the naturality conditions
  withTestOb2 @a @b $ withTestObExp @b @c $ do
    propIsoP
      (Exponential.curry @k @a @b @c)
      (Exponential.uncurry @b @c)

propClosed_
  :: forall k
   . (Testable k, Exponential.Closed k, TestOb (Monoidal.Unit @k), TestObIsOb k)
  => TestTree
propClosed_ =
  propClosed @k
    (\ @a @b r -> Monoidal.withOb2 @k @a @b r)
    (\ @a @b r -> Exponential.withObExp @k @a @b r)

propProfunctor :: forall {j} {k} (p :: j +-> k). (TestableProfunctor p) => TestTree
propProfunctor = testProperty "Profunctor" $ do
  Some @a <- genOb @k
  Some @b <- genOb @j
  p <- genP @(p a b)
  testEq "identity" "dimap id id p" (dimap id id p) "p" p
  Some @c <- genOb @k
  Some @d <- genOb @j
  f <- genP @(c ~> a)
  g <- genP @(b ~> d)
  testEq "interchange" "lmap f (rmap g p)" (lmap f (rmap g p)) "rmap g (lmap f p)" (rmap g (lmap f p))
  Some @e <- genOb @k
  Some @h <- genOb @j
  f' <- genP @(e ~> c)
  g' <- genP @(d ~> h)
  testEq
    "composition"
    "dimap (f . f') (g' . g) p"
    (dimap (f . f') (g' . g) p)
    "dimap f' g' (dimap f g p)"
    (dimap f' g' (dimap f g p))

propIso :: forall {k} (a :: k) b. (Testable k, TestOb a, TestOb b) => a ~> b -> b ~> a -> Property ()
propIso f g = do
  testEq "right inverse" "f . g" (f . g) "id" id
  testEq "left inverse" "g . f" (g . f) "id" id

propIsoP
  :: forall p q a b c d
   . (TestableProfunctor p, TestableProfunctor q, TestOb a, TestOb b, TestOb c, TestOb d)
  => (p a b -> q c d) -> (q c d -> p a b) -> Property ()
propIsoP f g = do
  p <- genP @(p a b)
  testEq "left inverse" "g (f p)" (g (f p)) "p" p
  q <- genP @(q c d)
  testEq "right inverse" "f (g q)" (f (g q)) "q" q

propMonoid
  :: forall {k} m
   . (Testable k, Monoid.Monoid (m :: k), TestOb m, TestOb (Monoidal.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a Monoidal.** b)) => r) -> r)
  -> TestTree
propMonoid withTestOb2 = testProperty ("Monoid " ++ showOb @k @m) $
  withTestOb2 @Monoidal.Unit @m $
    withTestOb2 @m @Monoidal.Unit $ do
      testEq
        "left identity"
        "μ . (η ⊗ 1)"
        (Monoid.mappend . (Monoid.mempty @m `Monoidal.par` obj @m))
        "λ"
        (Monoidal.leftUnitor @k @m)
      testEq
        "right identity"
        "μ . (1 ⊗ η)"
        (Monoid.mappend . (obj @m `Monoidal.par` Monoid.mempty @m))
        "ρ"
        (Monoidal.rightUnitor @k @m)
      withTestOb2 @m @m $ withTestOb2 @(m Monoidal.** m) @m $ do
        testEq
          "associativity"
          "μ . (μ ⊗ 1)"
          (Monoid.mappend @m . (Monoid.mappend @m `Monoidal.par` obj @m))
          "μ . (1 ⊗ μ) . α"
          (Monoid.mappend . (obj @m `Monoidal.par` Monoid.mappend @m) . Monoidal.associator @k @m @m @m)

propMonoid_
  :: forall {k} m
   . (Testable k, Monoid.Monoid (m :: k), TestOb m, TestOb (Monoidal.Unit @k), TestObIsOb k)
  => TestTree
propMonoid_ = propMonoid @m (\ @a @b r -> Monoidal.withOb2 @k @a @b r)
