{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Hypergraph where

import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat)
import Prelude (($))

import Proarrow.Category (Supplies)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), (==))
import Proarrow.Category.Monoidal.Strictified (Strictified (..), obj1, singleton, swap2)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj)
import Proarrow.Monoid (Comonoid (..), Monoid (..), comultS, mappendS)
import Proarrow.Object.Dual (CompactClosed)

type family NFold (n :: Nat) (x :: k) :: k where
  NFold Z x = Unit
  NFold (S n) x = x ** NFold n x

type family NFoldS (n :: Nat) (x :: k) :: [k] where
  NFoldS Z x = '[]
  NFoldS (S n) x = x ': NFoldS n x

withObNFold :: forall {k} n (a :: k) r. (SNatI n, Ob a, Monoidal k) => ((Ob (NFold n a)) => r) -> r
withObNFold r = case snat @n of
  SZ -> r
  SS @n' -> withObNFold @n' @a (withOb2 @k @a @(NFold n' a) r)

fanIn :: forall n a. (SNatI n, Monoid a) => NFold n a ~> a
fanIn = case snat @n of
  SZ -> mempty
  SS @n' -> mappend @a . (obj @a ** fanIn @n' @a)

fanInS :: forall n a. (SNatI n, Monoid a) => NFoldS n a ~> '[a]
fanInS =
  case snat @n of
    SZ -> Str mempty
    SS @n' -> mappendS @a . (obj1 @a ** fanInS @n' @a)

fanOut :: forall n a. (SNatI n, Comonoid a) => a ~> NFold n a
fanOut = case snat @n of
  SZ -> counit
  SS @n' -> (obj @a ** fanOut @n' @a) . comult @a

fanOutS :: forall n a. (SNatI n, Comonoid a) => '[a] ~> NFoldS n a
fanOutS =
  case snat @n of
    SZ -> Str counit
    SS @n' -> (obj1 @a ** fanOutS @n' @a) . comultS @a

-- | We have a special frobenius algebra for an object if it is a monoid and a comonoid in a nice compatible way.
-- Then there's a unique way to go from n-fold @a@ to m-fold @a@.
class (Monoid a, Comonoid a) => Frobenius a

spider :: forall n m a. (Frobenius a, SNatI n, SNatI m) => NFold n a ~> NFold m a
spider = fanOut @m @a . fanIn @n @a

spiderS :: forall n m a. (Frobenius a, SNatI n, SNatI m) => NFoldS n a ~> NFoldS m a
spiderS = fanOutS @m @a . fanInS @n @a

cup :: (Frobenius a) => Unit ~> a ** a
cup @a = comult @a . mempty @a

cupS :: (Frobenius a) => '[] ~> [a, a]
cupS @a = Str (cup @a)

cap :: (Frobenius a) => a ** a ~> Unit
cap @a = counit @a . mappend @a

capS :: (Frobenius a) => [a, a] ~> '[]
capS @a = Str (cap @a)

-- | A hypergraph category has a special frobenius algebra for every object, and the
-- frobenius algebra of any tensor product X ⊗ Y is induced in the canonical way from those of X and Y.
class (k `Supplies` Frobenius, CompactClosed k) => Hypergraph k

-- | A hypergraph category is self-dual compact closed.
dualHG :: forall {k} (a :: k) b. (Hypergraph k) => a ~> b -> b ~> a
dualHG f =
  unStr @'[b] @'[a] $
    cupS ** obj1
      == obj1 ** singleton f ** obj1
      == obj1 ** capS
      \\ f

linDistHG :: forall {k} (a :: k) b c. (Hypergraph k, Ob a, Ob b) => a ** b ~> c -> a ~> b ** c
linDistHG f =
  unStr @'[a] @[b, c] $
    obj1 ** cupS
      == Str @[a, b] @'[c] f ** obj1
      == swap2
      \\ f

linDistInvHG :: forall {k} (a :: k) b c. (Hypergraph k, Ob b, Ob c) => a ~> b ** c -> a ** b ~> c
linDistInvHG f =
  unStr @[a, b] @'[c] $
    swap2
      == obj1 ** Str @'[a] @[b, c] f
      == capS ** obj1
      \\ f

-- | A hypergraph category has a trace.
traceHG :: forall {k} u (x :: k) y. (Hypergraph k, Ob x, Ob y, Ob u) => u ** x ~> u ** y -> x ~> y
traceHG f =
  unStr $
    cupS ** obj1
      == obj1 ** Str @[u, x] @'[u, y] f
      == capS ** obj1

-- | A hypergraph category is monoidal closed.
type ExpHG a b = a ** b

curryHG :: forall {k} (a :: k) b c. (Hypergraph k, Ob a, Ob b) => a ** b ~> c -> a ~> ExpHG b c
curryHG = linDistHG @a @b @c

applyHG :: forall {k} (b :: k) c. (Hypergraph k, Ob b, Ob c) => ExpHG b c ** b ~> c
applyHG = linDistInvHG @_ @b (obj @b ** obj @c)