{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Hypergraph where

import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat)

import Proarrow.Category (Supplies)
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , leftUnitorInvWith
  , leftUnitorWith
  , par
  , rightUnitorInvWith
  , rightUnitorWith
  , (==)
  , (||)
  )
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.Dual (CompactClosed)

type family NFold (n :: Nat) (x :: k) :: k where
  NFold Z x = Unit
  NFold (S n) x = x ** NFold n x

withObNFold :: forall {k} n (a :: k) r. (SNatI n, Ob a, Monoidal k) => ((Ob (NFold n a)) => r) -> r
withObNFold r = case snat @n of
  SZ -> r
  SS @n' -> withObNFold @n' @a (withOb2 @k @a @(NFold n' a) r)

fanIn :: forall n a. (SNatI n, Monoid a) => NFold n a ~> a
fanIn = case snat @n of
  SZ -> mempty
  SS @n' -> mappend @a . (obj @a `par` fanIn @n' @a)

fanOut :: forall n a. (SNatI n, Comonoid a) => a ~> NFold n a
fanOut = case snat @n of
  SZ -> counit
  SS @n' -> (obj @a `par` fanOut @n' @a) . comult @a

-- | We have a special frobenius algebra for an object if it is a monoid and a comonoid in a nice compatible way.
-- Then there's a unique way to go from n-fold @a@ to m-fold @a@.
class (Monoid a, Comonoid a) => Frobenius a where
  spider :: (SNatI n, SNatI m) => NFold n a ~> NFold m a

cup :: (Frobenius a) => Unit ~> a ** a
cup @a = comult @a . mempty @a

cap :: (Frobenius a) => a ** a ~> Unit
cap @a = counit @a . mappend @a

-- | Since spider has a (very) ambiguous type, it's not possible to give a default implementation.
-- Use this function to provide the implementation as follows:
--
-- > spider @n @m = spiderDefault @n @m @a
spiderDefault :: forall n m a. (Monoid a, Comonoid a, SNatI n, SNatI m) => NFold n a ~> NFold m a
spiderDefault = fanOut @m @a . fanIn @n @a

-- | A hypergraph category has a special frobenius algebra for every object, and the
-- frobenius algebra of any tensor product X ⊗ Y is induced in the canonical way from those of X and Y.
class (k `Supplies` Frobenius, CompactClosed k) => Hypergraph k

-- | A hypergraph category is self-dual compact closed.
dualHG :: forall {k} (a :: k) b. (Hypergraph k) => a ~> b -> b ~> a
dualHG f =
  leftUnitorInvWith (cup @a)
    == obj @a || f || obj @b
    == associator @k @a @b @b
    == rightUnitorWith (cap @b)
    \\ f

linDistHG :: forall {k} (a :: k) b c. (Hypergraph k, Ob a, Ob b) => a ** b ~> c -> a ~> b ** c
linDistHG f =
  rightUnitorInvWith (cup @b)
    == associatorInv @k @a @b @b
    == f || obj @b
    == swap @k @c @b
    \\ f

linDistInvHG :: forall {k} (a :: k) b c. (Hypergraph k, Ob b, Ob c) => a ~> b ** c -> a ** b ~> c
linDistInvHG f =
  swap @k @a @b
    == obj @b || f
    == associatorInv @k @b @b @c
    == leftUnitorWith (cap @b)
    \\ f

-- | A hypergraph category has a trace
traceHG :: forall {k} u (x :: k) y. (Hypergraph k, Ob x, Ob y, Ob u) => u ** x ~> u ** y -> x ~> y
traceHG f =
  leftUnitorInvWith (cup @u)
    == associator @k @u @u @x
    == obj @u || f
    == associatorInv @k @u @u @y
    == leftUnitorWith (cap @u)

type ExpHG a b = a ** b

curryHG :: forall {k} (a :: k) b c. (Hypergraph k, Ob a, Ob b) => a ** b ~> c -> a ~> ExpHG b c
curryHG = linDistHG @a @b @c

applyHG :: forall {k} (b :: k) c. (Hypergraph k, Ob b, Ob c) => ExpHG b c ** b ~> c
applyHG = linDistInvHG @_ @b (obj @b `par` obj @c)