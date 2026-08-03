module Proarrow.Category.Instance.Span where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph (ExpHG, Frobenius, Hypergraph, applyHG, curryHG)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasBiproducts (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), WrappedOb, dimapDefault, src)
import Proarrow.Limit.BinaryProduct
  ( HasBinaryProducts (..)
  , HasProducts
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  )
import Proarrow.Limit.Exponential (Closed (..))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Profunctor.Cocone (Cocone (..), Sink (..))
import Proarrow.Profunctor.Cone (Cone (..), Cosink (..))

newtype SPAN k = SP k

type Span :: CAT (SPAN k)
data Span a b where
  Span :: forall c a b. c ~> a -> c ~> b -> Span (SP a) (SP b)

arr :: (CategoryOf k) => (a :: k) ~> b -> Span (SP a) (SP b)
arr f = Span (src f) f

coarr :: (CategoryOf k) => (a :: k) ~> b -> Span (SP b) (SP a)
coarr f = Span f (src f)

instance (HasPullbacks k) => Profunctor (Span :: CAT (SPAN k)) where
  dimap = dimapDefault
  r \\ Span f g = r \\ f \\ g
instance (HasPullbacks k) => Promonad (Span :: CAT (SPAN k)) where
  id = Span id id
  Span f g . Span h i = case pullback i f of Cone (Leg l (Leg r Apex)) -> Span (h . l) (g . r)
instance (HasPullbacks k) => CategoryOf (SPAN k) where
  type (~>) = Span
  type Ob a = WrappedOb SP a

instance (HasPullbacks k, HasProducts k) => MonoidalProfunctor (Span :: CAT (SPAN k)) where
  one = id
  Span l1 l2 ** Span r1 r2 = Span (l1 *** r1) (l2 *** r2)
instance (HasPullbacks k, HasProducts k) => Monoidal (SPAN k) where
  type SP a ** SP b = SP (a && b)
  type Unit = SP TerminalObject
  withOb2 @(SP a) @(SP b) r = withObProd @k @a @b r
  leftUnitor = arr leftUnitorProd
  leftUnitorInv = arr leftUnitorProdInv
  rightUnitor = arr rightUnitorProd
  rightUnitorInv = arr rightUnitorProdInv
  associator @(SP a) @(SP b) @(SP c) = arr (associatorProd @a @b @c)
  associatorInv @(SP a) @(SP b) @(SP c) = arr (associatorProdInv @a @b @c)
instance (HasPullbacks k, HasProducts k) => SymMonoidal (SPAN k) where
  swap @(SP a) @(SP b) = arr (swapProd @a @b)

instance (HasPullbacks k, HasProducts k, Ob a) => Monoid (SP (a :: k)) where
  mempty = coarr terminate
  mappend = coarr (id &&& id)
instance (HasPullbacks k, HasProducts k, Ob a) => Comonoid (SP (a :: k)) where
  counit = arr terminate
  comult = arr (id &&& id)
instance (HasPullbacks k, HasProducts k, Ob a) => Frobenius (SP (a :: k))
instance (HasPullbacks k, HasProducts k) => Hypergraph (SPAN k)
instance (HasPullbacks k, HasProducts k) => CopyDiscard (SPAN k)

instance (HasPullbacks k, HasProducts k) => Closed (SPAN k) where
  type a ~~> b = ExpHG a b
  withObExp @(SP a) @(SP b) r = withObProd @k @a @b r
  curry @a @b = curryHG @a @b
  apply @b @c = applyHG @b @c

instance (HasPullbacks k, HasProducts k) => StarAutonomous (SPAN k) where
  type Dual a = a
  dual (Span f g) = Span g f
  dualInv (Span f g) = Span g f
  linDist @(SP a) @(SP b) (Span f g) = Span (fst @k @a @b . f) (snd @k @a @b . f &&& g)
  linDistInv @_ @(SP b) @(SP c) (Span f g) = Span (f &&& fst @k @b @c . g) (snd @k @b @c . g)
instance (HasPullbacks k, HasProducts k) => CompactClosed (SPAN k) where
  distribDual @(SP a) @(SP b) = withObProd @k @a @b id
  dualUnit = id

instance (HasPullbacks k, HasProducts k) => DaggerProfunctor (Span :: CAT (SPAN k)) where
  dagger = dual

instance (HasPullbacks k, HasBinaryCoproducts k) => HasBinaryProducts (SPAN k) where
  type SP a && SP b = SP (a || b)
  withObProd @(SP a) @(SP b) r = withObCoprod @k @a @b r
  fst @(SP a) @(SP b) = coarr (lft @k @a @b)
  snd @(SP a) @(SP b) = coarr (rgt @k @a @b)
  Span f g &&& Span h i = Span (f ||| h) (g +++ i)

instance (HasPullbacks k, HasBinaryCoproducts k) => HasBinaryCoproducts (SPAN k) where
  type SP a || SP b = SP (a || b)
  withObCoprod @(SP a) @(SP b) r = withObCoprod @k @a @b r
  lft @(SP a) @(SP b) = arr (lft @k @a @b)
  rgt @(SP a) @(SP b) = arr (rgt @k @a @b)
  Span f g ||| Span h i = Span (f +++ h) (g ||| i)

instance (HasPullbacks k, HasBinaryCoproducts k) => HasBiproducts (SPAN k) where
  Span f g `sum` Span h i = Span (f ||| h) (g ||| i)

instance (HasPullbacks k) => HasPushouts (SPAN k) where
  pushout (Span f g) (Span h i) = case pullback f h of
    Cone (Leg l (Leg r Apex)) -> Cocone (Coleg (coarr (g . l)) (Coleg (coarr (i . r)) Coapex))
instance (HasPullbacks k) => HasPullbacks (SPAN k) where
  pullback (Span f g) (Span h i) = case pullback g i of
    Cone (Leg l (Leg r Apex)) -> Cone (Leg (arr (f . l)) (Leg (arr (h . r)) Apex))
