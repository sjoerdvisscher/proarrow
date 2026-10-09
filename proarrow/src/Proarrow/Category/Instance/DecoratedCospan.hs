-- | __Decorated cospans__ in @k@: a morphism @a '~>' b@ is a cospan @a -> x <- b@ together with a
-- decoration of its apex, a value of @f x@. Composition glues along a pushout and joins the two
-- decorations on the glued apex, using the 'Alternative' structure of @f@, which takes decorations
-- on two objects to one on their coproduct. As for "Proarrow.Category.Instance.Cospan", the
-- coproduct of @k@ is the tensor and every object is a Frobenius monoid, so this is a
-- 'Hypergraph' category.
--
-- With labelled boxes as the decoration, a morphism is an open hypergraph: see
-- "Proarrow.Category.Instance.OpenHypergraph".
module Proarrow.Category.Instance.DecoratedCospan where

import Data.Kind (Type)

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Applicative (Alternative (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..))
import Proarrow.Category.Monoidal.Hypergraph (ExpHG, Frobenius, Hypergraph, Sized (..), applyHG, cap, cup, curryHG)
import Proarrow.Category.Monoidal.IsoMix (IsoMix (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Colimit.BinaryCoproduct
  ( HasBinaryCoproducts (..)
  , HasCoproducts
  , associatorCoprod
  , associatorCoprodInv
  , leftUnitorCoprod
  , leftUnitorCoprodInv
  , rightUnitorCoprod
  , rightUnitorCoprodInv
  , swapCoprod
  )
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), WrappedOb, dimapDefault, tgt)
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid (..), Monoid (..))

type data DECCOSPAN (f :: k -> Type) = DC k

type DecCospan :: CAT (DECCOSPAN f)
data DecCospan a b where
  DecCospan :: forall {k} {f :: k -> Type} c a b. a ~> c -> b ~> c -> f c -> DecCospan (DC a :: DECCOSPAN f) (DC b)

-- | A morphism of @k@ as a cospan with the empty decoration.
arr :: forall {k} (f :: k -> Type) a b. (Alternative f) => a ~> b -> DecCospan (DC a :: DECCOSPAN f) (DC b)
arr f = DecCospan f (tgt f) (empty ()) \\ f

-- | A morphism of @k@ as a cospan the other way round, with the empty decoration.
coarr :: forall {k} (f :: k -> Type) a b. (Alternative f) => a ~> b -> DecCospan (DC b :: DECCOSPAN f) (DC a)
coarr f = DecCospan (tgt f) f (empty ()) \\ f

instance (HasPushouts k, Alternative f) => Profunctor (DecCospan :: CAT (DECCOSPAN (f :: k -> Type))) where
  dimap = dimapDefault
  r \\ DecCospan f g _ = r \\ f \\ g
instance (HasPushouts k, Alternative f) => Promonad (DecCospan :: CAT (DECCOSPAN (f :: k -> Type))) where
  id = arr id
  DecCospan f g s . DecCospan h i t = pushout i f \l r -> DecCospan (l . h) (r . g) (alt (l ||| r) (t, s)) \\ i \\ f

-- | The category of decorated cospans in @k@: an arrow @'DC' a '~>' 'DC' b@ is a pair of arrows
-- @a '~>' x@ and @b '~>' x@ into a common object, with a decoration of @x@.
instance (HasPushouts k, Alternative f) => CategoryOf (DECCOSPAN (f :: k -> Type)) where
  type (~>) = DecCospan
  type Ob a = WrappedOb DC a

instance (HasPushouts k, HasCoproducts k, Alternative f) => MonoidalProfunctor (DecCospan :: CAT (DECCOSPAN (f :: k -> Type))) where
  one = id
  DecCospan @c1 l1 l2 s ** DecCospan @c2 r1 r2 t =
    withObCoprod @k @c1 @c2 (DecCospan (l1 +++ r1) (l2 +++ r2) (alt id (s, t))) \\ l1 \\ r1
instance (HasPushouts k, HasCoproducts k, Alternative f) => Monoidal (DECCOSPAN (f :: k -> Type)) where
  type DC a ** DC b = DC (a || b)
  type Unit = DC InitialObject
  withOb2 @(DC a) @(DC b) r = withObCoprod @k @a @b r
  leftUnitor = arr leftUnitorCoprod
  leftUnitorInv = arr leftUnitorCoprodInv
  rightUnitor = arr rightUnitorCoprod
  rightUnitorInv = arr rightUnitorCoprodInv
  associator @(DC a) @(DC b) @(DC c) = arr (associatorCoprod @a @b @c)
  associatorInv @(DC a) @(DC b) @(DC c) = arr (associatorCoprodInv @a @b @c)
instance (HasPushouts k, HasCoproducts k, Alternative f) => SymMonoidal (DECCOSPAN (f :: k -> Type)) where
  swap @(DC a) @(DC b) = arr (swapCoprod @a @b)

instance (HasPushouts k, HasCoproducts k, Alternative f, Ob a) => Monoid (DC a :: DECCOSPAN (f :: k -> Type)) where
  mempty = arr initiate
  mappend = arr (id ||| id)
instance (HasPushouts k, HasCoproducts k, Alternative f, Ob a) => CommutativeMonoid (DC a :: DECCOSPAN (f :: k -> Type))
instance (HasPushouts k, HasCoproducts k, Alternative f, Ob a) => Comonoid (DC a :: DECCOSPAN (f :: k -> Type)) where
  counit = coarr initiate
  comult = coarr (id ||| id)
instance (HasPushouts k, HasCoproducts k, Alternative f, Ob a) => CocommutativeComonoid (DC a :: DECCOSPAN (f :: k -> Type))
instance (HasPushouts k, HasCoproducts k, Alternative f, Ob a) => Frobenius (DC a :: DECCOSPAN (f :: k -> Type))
instance (HasPushouts k, HasCoproducts k, Alternative f) => Hypergraph (DECCOSPAN (f :: k -> Type))
instance (HasPushouts k, HasCoproducts k, Alternative f) => CopyDiscard (DECCOSPAN (f :: k -> Type))
instance (HasPushouts k, Alternative f) => Sized (DECCOSPAN (f :: k -> Type)) where
  sizeOf = 2

instance (HasPushouts k, HasCoproducts k, Alternative f) => Closed (DECCOSPAN (f :: k -> Type)) where
  type a ~~> b = ExpHG a b
  withObExp @(DC a) @(DC b) r = withObCoprod @k @a @b r
  curry @a @b = curryHG @a @b
  apply @b @c = applyHG @b @c

instance (HasPushouts k, HasCoproducts k, Alternative f) => Dialogue (DECCOSPAN (f :: k -> Type)) where
  type Dual a = a
  withObDual r = r
  dual = dagger
  linDist @(DC a) @(DC b) (DecCospan f g s) = DecCospan (f . lft @k @a @b) (f . rgt @k @a @b ||| g) s
  linDistInv @_ @(DC b) @(DC c) (DecCospan f g s) = DecCospan (f ||| g . lft @k @b @c) (g . rgt @k @b @c) s
  doubleNegInv = id

instance (HasPushouts k, HasCoproducts k, Alternative f) => StarAutonomous (DECCOSPAN (f :: k -> Type)) where
  dualInv = dagger
  doubleNeg = id
instance (HasPushouts k, HasCoproducts k, Alternative f) => IsoMix (DECCOSPAN (f :: k -> Type)) where
  dualUnit = id
  dualUnitInv = id
  dualityCounit @a = cap @a

instance (HasPushouts k, HasCoproducts k, Alternative f) => CompactClosed (DECCOSPAN (f :: k -> Type)) where
  distribDual @(DC a) @(DC b) = withObCoprod @k @a @b id
  dualityUnit @a = cup @a

instance (HasPushouts k, Alternative f) => DaggerProfunctor (DecCospan :: CAT (DECCOSPAN (f :: k -> Type))) where
  dagger (DecCospan f g s) = DecCospan g f s
