{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Hypergraph categories: compact closed categories where every object carries a 'Frobenius'
-- structure (a compatible 'Proarrow.Monoid.Monoid' and 'Proarrow.Monoid.Comonoid'), giving n-to-m
-- 'spider's, 'cup's and 'cap's. This is the setting for string diagrams with arbitrary
-- fan-in\/fan-out such as "Proarrow.Category.Instance.ZX".
module Proarrow.Category.Monoidal.Hypergraph where

import Data.Kind (Constraint)
import Data.Type.Nat (SNatI)
import Prelude (($))

import Proarrow.Category.Instance.Free (FREE)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), NFold, NFoldS, SymMonoidal (..), (==))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed)
import Proarrow.Category.Monoidal.Strictified (Strictified (..), obj1, singleton, swap2)
import Proarrow.Core (CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj)
import Proarrow.Monoid
  ( CocommutativeComonoid
  , CommutativeMonoid
  , Comonoid (..)
  , Monoid (..)
  , Supplies
  , fanIn
  , fanInS
  , fanOut
  , fanOutS
  )
import Proarrow.Tools.Laws (Law (..), Laws (..), (===))

-- | A __special commutative Frobenius algebra__: a commutative monoid and cocommutative comonoid
-- satisfying speciality (@mappend . comult = id@) and the Frobenius law. A 'Hypergraph' category
-- supplies this structure at every object, and with it the 'spider' from n-fold @a@ to m-fold @a@
-- is the unique connected map (commutativity\/cocommutativity make
-- 'fanIn'\/'fanOut' independent of wiring order). The bare notion of a Frobenius monoid needs
-- neither (co)commutativity, but the library only ever uses the special commutative one.
class (CommutativeMonoid a, CocommutativeComonoid a) => Frobenius a

instance (forall (a :: k). (Ob a) => Frobenius a) => Supplies Frobenius k

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
class (Supplies Frobenius k, CompactClosed k) => Hypergraph k

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

-- | In the free category the supply generators (see @'Supplies' 'Monoid'@\/@'Supplies' 'Comonoid'@
-- in "Proarrow.Monoid") are compatible by fiat, so monoid + comonoid is already 'Frobenius'. With
-- both supplies in @cs@, @'Supplies' 'Frobenius'@ and 'Hypergraph' are derived, with no structure
-- of their own. Superclasses are taken directly as the context to keep dictionary construction
-- acyclic. Bundling them into an 'Proarrow.Category.Instance.Free.All'-style constraint here builds
-- a dictionary that references itself through the quantified 'Supplies' constraint, looping at
-- runtime.
instance (CommutativeMonoid a, CocommutativeComonoid (a :: FREE cs p)) => Frobenius (a :: FREE cs p)

instance (Supplies Frobenius (FREE cs p), CompactClosed (FREE cs p)) => Hypergraph (FREE cs p)

-- | The structures the laws of a category supplying special commutative Frobenius algebras are
-- stated for: the monoids and comonoids, together.
type FrobeniusStructures :: [Kind -> Constraint]
type FrobeniusStructures = '[Monoidal, SymMonoidal, Supplies Monoid, Supplies Comonoid]

-- | The supplied monoids and comonoids are special and satisfy the Frobenius law. Their monoid and
-- comonoid laws, and their commutativity, are separate instances, in "Proarrow.Monoid".
instance Laws FrobeniusStructures where
  laws =
    [ Law "speciality" \ @a _ -> obj @a === mappend @a . comult @a
    , Law "Frobenius (left)" \ @a _ ->
        withOb2 @_ @a @a $
          comult @a . mappend @a === (mappend @a ** obj @a) . associatorInv @_ @a @a @a . (obj @a ** comult @a)
    , Law "Frobenius (right)" \ @a _ ->
        withOb2 @_ @a @a $
          comult @a . mappend @a === (obj @a ** mappend @a) . associator @_ @a @a @a . (comult @a ** obj @a)
    ]
