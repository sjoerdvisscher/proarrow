{-# LANGUAGE AllowAmbiguousTypes #-}

module Props where

import Control.Monad (when)
import Test.Tasty (TestTree)
import Test.Tasty.Falsify (Property, testFailed, testProperty)
import Prelude hiding (elem, fst, id, snd, (.), (>>))

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, obj, rmap, type (+->))
import Proarrow.Object.BinaryCoproduct qualified as BinaryCoproduct
import Proarrow.Object.BinaryProduct qualified as BinaryProduct
import Proarrow.Object.Initial qualified as Initial
import Proarrow.Object.Terminal qualified as Terminal

import Proarrow.Category.Monoidal qualified as M
import Proarrow.Monoid qualified as Monoid
import Proarrow.Object.Exponential qualified as Exponential
import Testable (Some (..), TestObIsOb, Testable (..), TestableProfunctor, TestableType (..), genP)

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
propTerminalObject = testProperty "Terminal object" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genP @(a ~> b)
  testEq "uniqueness" "terminate . f" (Terminal.terminate . f) "terminate" Terminal.terminate

propInitialObject
  :: forall k
   . (Testable k, Initial.HasInitialObject k, TestOb (Initial.InitialObject :: k))
  => TestTree
propInitialObject = testProperty "Initial object" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  f <- genP @(a ~> b)
  testEq "uniqueness" "f . initiate" (f . Initial.initiate) "initiate" Initial.initiate

propBinaryProducts
  :: forall k
   . (Testable k, BinaryProduct.HasBinaryProducts k)
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a BinaryProduct.&& b)) => r) -> r)
  -> TestTree
propBinaryProducts withTestObProd = testProperty "Binary products" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  Some @z <- genOb
  withTestObProd @b @c $ do
    f <- genP @(a ~> b)
    g <- genP @(a ~> c)
    testEq "fst" "fst . (f &&& g)" (BinaryProduct.fst @k @b @c . (f BinaryProduct.&&& g)) "f" f
    testEq "snd" "snd . (f &&& g)" (BinaryProduct.snd @k @b @c . (f BinaryProduct.&&& g)) "g" g
    h <- genP @(z ~> a)
    testEq "uniqueness" "(f . h) &&& (g . h)" ((f . h) BinaryProduct.&&& (g . h)) "(f &&& g) . h" ((f BinaryProduct.&&& g) . h)

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
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  Some @z <- genOb
  withTestObCoprod @a @b $ do
    f <- genP @(a ~> c)
    g <- genP @(b ~> c)
    testEq "lft" "(f ||| g) . lft" ((f BinaryCoproduct.||| g) . BinaryCoproduct.lft @k @a @b) "f" f
    testEq "rgt" "(f ||| g) . rtg" ((f BinaryCoproduct.||| g) . BinaryCoproduct.rgt @k @a @b) "g" g
    h <- genP @(c ~> z)
    testEq "uniqueness" "(h . f) ||| (h . g)" ((h . f) BinaryCoproduct.||| (h . g)) "h . (f ||| g)" (h . (f BinaryCoproduct.||| g))

propBinaryCoproducts_
  :: forall k
   . (Testable k, BinaryCoproduct.HasBinaryCoproducts k, TestObIsOb k)
  => TestTree
propBinaryCoproducts_ = propBinaryCoproducts @k (\ @a @b r -> BinaryCoproduct.withObCoprod @k @a @b r)

propMonoidal
  :: forall k
   . (Testable k, M.Monoidal k, TestOb (M.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a M.** b)) => r) -> r)
  -> TestTree
propMonoidal withTestOb2 = testProperty "Monoidal" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  Some @d <- genOb
  -- f <- genP @(a ~> b)
  -- g <- genP @(b ~> c)
  -- h <- genP @(c ~> d)
  withTestOb2 @a @b
    $ withTestOb2 @b @c
    $ withTestOb2 @c @d
    $ withTestOb2 @M.Unit @a
    $ withTestOb2 @M.Unit @b
    $ withTestOb2 @a @M.Unit
    $ withTestOb2 @b @M.Unit
    $ withTestOb2 @(a M.** M.Unit) @b
    $ withTestOb2 @(a M.** b) @c
    $ withTestOb2 @a @(b M.** c)
    $ withTestOb2 @(b M.** c) @d
    $ withTestOb2 @b @(c M.** d)
    $ withTestOb2 @a @(b M.** (c M.** d))
    $ withTestOb2 @((a M.** b) M.** c) @d
    $ do
      propIso (M.associator @k @a @b @c) (M.associatorInv @k @a @b @c)
      propIso (M.leftUnitor @k @a) (M.leftUnitorInv @k @a)
      propIso (M.rightUnitor @k @a) (M.rightUnitorInv @k @a)
      -- [ associator . ((f `par` g) `par` h) :=: (f `par` (g `par` h)) . associator
      --       , associatorInv . (f `par` (g `par` h)) :=: ((f `par` g) `par` h) . associatorInv
      --       , leftUnitor . (par0 `par` f) :=: f . leftUnitor
      --       , leftUnitorInv . f :=: (par0 `par` f) . leftUnitorInv
      --       , rightUnitor . (f `par` par0) :=: f . rightUnitor
      --       , rightUnitorInv . f :=: (f `par` par0) . rightUnitorInv
      --       , (id `par` leftUnitor) . associator @_ @(EMB "A") @_ @(EMB "B") :=: rightUnitor `par` id
      --       , (id `par` associator @_ @(EMB "B") @(EMB "C") @(EMB "D"))
      --           . associator
      --           . (associator @_ @(EMB "A") @(EMB "B") @(EMB "C") `par` id)
      --           :=: associator . associator
      --       ]

propMonoidal_
  :: forall k
   . (Testable k, M.Monoidal k, TestOb (M.Unit @k), TestObIsOb k)
  => TestTree
propMonoidal_ = propMonoidal @k (\ @a @b r -> M.withOb2 @k @a @b r)

propSymMonoidal
  :: forall k
   . (Testable k, M.SymMonoidal k, TestOb (M.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a M.** b)) => r) -> r)
  -> TestTree
propSymMonoidal withTestOb2 = testProperty "Symmetric monoidal" $ do
  Some @a <- genOb @k
  Some @b <- genOb
  Some @c <- genOb
  withTestOb2 @a @b
    $ withTestOb2 @b @c
    $ withTestOb2 @c @a
    $ withTestOb2 @(a M.** b) @c
    $ withTestOb2 @b @(c M.** a)
    $ do
      testEq "swap swap" "swap . swap" (M.swap @k @b @a . M.swap @k @a @b) "id" id
      testEq "hexagon identity"
        "associator . swap . associator" (M.associator @k @b @c @a . M.swap @k @a @(b M.** c) . M.associator @k @a @b @c)
        "(swap `par` id) . associator . (id `par` swap)" ((obj @b `M.par` M.swap @k @a @c) . M.associator @k @b @a @c . (M.swap @k @a @b `M.par` obj @c))

propSymMonoidal_
  :: forall k
   . (Testable k, M.SymMonoidal k, TestOb (M.Unit @k), TestObIsOb k)
  => TestTree
propSymMonoidal_ = propSymMonoidal @k (\ @a @b r -> M.withOb2 @k @a @b r)

propClosed
  :: forall k
   . (Testable k, Exponential.Closed k, TestOb (M.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a M.** b)) => r) -> r)
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
   . (Testable k, Exponential.Closed k, TestOb (M.Unit @k), TestObIsOb k)
  => TestTree
propClosed_ =
  propClosed @k
    (\ @a @b r -> M.withOb2 @k @a @b r)
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
   . (Testable k, Monoid.Monoid (m :: k), TestOb m, TestOb (M.Unit @k))
  => (forall (a :: k) b r. (TestOb a, TestOb b) => ((TestOb (a M.** b)) => r) -> r)
  -> TestTree
propMonoid withTestOb2 = testProperty ("Monoid " ++ showOb @k @m) $
  withTestOb2 @M.Unit @m $
    withTestOb2 @m @M.Unit $ do
      testEq
        "left identity"
        "μ . (η ⊗ 1)"
        (Monoid.mappend . (Monoid.mempty @m `M.par` obj @m))
        "λ"
        (M.leftUnitor @k @m)
      testEq
        "right identity"
        "μ . (1 ⊗ η)"
        (Monoid.mappend . (obj @m `M.par` Monoid.mempty @m))
        "ρ"
        (M.rightUnitor @k @m)
      withTestOb2 @m @m $ withTestOb2 @(m M.** m) @m $ do
        testEq
          "associativity"
          "μ . (μ ⊗ 1)"
          (Monoid.mappend @m . (Monoid.mappend @m `M.par` obj @m))
          "μ . (1 ⊗ μ) . α"
          (Monoid.mappend . (obj @m `M.par` Monoid.mappend @m) . M.associator @k @m @m @m)

propMonoid_
  :: forall {k} m
   . (Testable k, Monoid.Monoid (m :: k), TestOb m, TestOb (M.Unit @k), TestObIsOb k)
  => TestTree
propMonoid_ = propMonoid @m (\ @a @b r -> M.withOb2 @k @a @b r)
