module Proarrow.Category.Instance.Cospan where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Span (SPAN (..), Span (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph (ExpHG, Frobenius (..), Hypergraph, applyHG, curryHG, spiderDefault)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, tgt, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct
  ( HasBinaryCoproducts (..)
  , associatorCoprod
  , associatorCoprodInv
  , leftUnitorCoprod
  , leftUnitorCoprodInv
  , rightUnitorCoprod
  , rightUnitorCoprodInv
  , swapCoprod
  )
import Proarrow.Object.Dual (CompactClosed (..), StarAutonomous (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Pullback (Cone (..), Cosink (..), HasPullbacks (..))
import Proarrow.Object.Pushout (Cocone (..), HasPushouts (..), Sink (..))

newtype COSPAN k = CS k
type instance UN CS (CS k) = k

type Cospan :: CAT (COSPAN k)
data Cospan a b where
  Cospan :: forall c a b. a ~> c -> b ~> c -> Cospan (CS a) (CS b)

arr :: (CategoryOf k) => (a :: k) ~> b -> Cospan (CS a) (CS b)
arr f = Cospan f (tgt f)

coarr :: (CategoryOf k) => (a :: k) ~> b -> Cospan (CS b) (CS a)
coarr f = Cospan (tgt f) f

instance (HasPushouts k) => Profunctor (Cospan :: CAT (COSPAN k)) where
  dimap = dimapDefault
  r \\ Cospan f g = r \\ f \\ g
instance (HasPushouts k) => Promonad (Cospan :: CAT (COSPAN k)) where
  id = Cospan id id
  Cospan f g . Cospan h i = case pushout i f of Cocone (Coleg l (Coleg r Coapex)) -> Cospan (l . h) (r . g)
instance (HasPushouts k) => CategoryOf (COSPAN k) where
  type (~>) = Cospan
  type Ob a = (Is CS a, Ob (UN CS a))

instance (HasPushouts k) => MonoidalProfunctor (Cospan :: CAT (COSPAN k)) where
  par0 = id
  Cospan l1 l2 `par` Cospan r1 r2 = Cospan (l1 +++ r1) (l2 +++ r2)
instance (HasPushouts k) => Monoidal (COSPAN k) where
  type CS a ** CS b = CS (a || b)
  type Unit = CS InitialObject
  withOb2 @(CS a) @(CS b) r = withObCoprod @k @a @b r
  leftUnitor = arr leftUnitorCoprod
  leftUnitorInv = arr leftUnitorCoprodInv
  rightUnitor = arr rightUnitorCoprod
  rightUnitorInv = arr rightUnitorCoprodInv
  associator @(CS a) @(CS b) @(CS c) = arr (associatorCoprod @a @b @c)
  associatorInv @(CS a) @(CS b) @(CS c) = arr (associatorCoprodInv @a @b @c)
instance (HasPushouts k) => SymMonoidal (COSPAN k) where
  swap @(CS a) @(CS b) = arr (swapCoprod @a @b)

instance (HasPushouts k, Ob a) => Monoid (CS (a :: k)) where
  mempty = arr initiate
  mappend = arr (id ||| id)
instance (HasPushouts k, Ob a) => Comonoid (CS (a :: k)) where
  counit = coarr initiate
  comult = coarr (id ||| id)
instance (HasPushouts k, Ob a) => Frobenius (CS (a :: k)) where
  spider @x @y = spiderDefault @x @y @(CS a)
instance (HasPushouts k) => Hypergraph (COSPAN k)
instance (HasPushouts k) => CopyDiscard (COSPAN k)

instance (HasPushouts k) => Closed (COSPAN k) where
  type a ~~> b = ExpHG a b
  withObExp @(CS a) @(CS b) r = withObCoprod @k @a @b r
  curry @a @b = curryHG @a @b
  apply @b @c = applyHG @b @c

instance (HasPushouts k) => StarAutonomous (COSPAN k) where
  type Dual a = a
  dual (Cospan f g) = Cospan g f
  dualInv (Cospan f g) = Cospan g f
  linDist @(CS a) @(CS b) (Cospan f g) = Cospan (f . lft @k @a @b) (f . rgt @k @a @b ||| g)
  linDistInv @_ @(CS b) @(CS c) (Cospan f g) = Cospan (f ||| g . lft @k @b @c) (g . rgt @k @b @c)
instance (HasPushouts k) => CompactClosed (COSPAN k) where
  distribDual @(CS a) @(CS b) = withObCoprod @k @a @b id
  dualUnit = id

instance (HasPushouts k) => DaggerProfunctor (Cospan :: CAT (COSPAN k)) where
  dagger = dual

data family Pushout :: SPAN k +-> COSPAN k
instance (HasPushouts k, HasPullbacks k) => FunctorForRep (Pushout :: SPAN k +-> COSPAN k) where
  type Pushout @ (SP a) = CS a
  fmap (Span l r) = case pushout l r of Cocone (Coleg f (Coleg g Coapex)) -> Cospan f g

data family Pullback :: COSPAN k +-> SPAN k
instance (HasPushouts k, HasPullbacks k) => FunctorForRep (Pullback :: COSPAN k +-> SPAN k) where
  type Pullback @ (CS a) = SP a
  fmap (Cospan l r) = case pullback l r of Cone (Leg f (Leg g Apex)) -> Span f g
