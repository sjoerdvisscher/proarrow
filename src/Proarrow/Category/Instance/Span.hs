module Proarrow.Category.Instance.Span where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph (ExpHG, Frobenius (..), Hypergraph, applyHG, curryHG, spiderDefault)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, src)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  )
import Proarrow.Object.Dual (CompactClosed (..), StarAutonomous (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Pullback (Cone (..), Cosink (..), HasPullbacks (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))

newtype SPAN k = SP k
type instance UN SP (SP k) = k

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
  type Ob a = (Is SP a, Ob (UN SP a))

instance (HasPullbacks k) => MonoidalProfunctor (Span :: CAT (SPAN k)) where
  par0 = id
  Span l1 l2 `par` Span r1 r2 = Span (l1 *** r1) (l2 *** r2)
instance (HasPullbacks k) => Monoidal (SPAN k) where
  type SP a ** SP b = SP (a && b)
  type Unit = SP TerminalObject
  withOb2 @(SP a) @(SP b) r = withObProd @k @a @b r
  leftUnitor = arr leftUnitorProd
  leftUnitorInv = arr leftUnitorProdInv
  rightUnitor = arr rightUnitorProd
  rightUnitorInv = arr rightUnitorProdInv
  associator @(SP a) @(SP b) @(SP c) = arr (associatorProd @a @b @c)
  associatorInv @(SP a) @(SP b) @(SP c) = arr (associatorProdInv @a @b @c)
instance (HasPullbacks k) => SymMonoidal (SPAN k) where
  swap @(SP a) @(SP b) = arr (swapProd @a @b)

instance (HasPullbacks k, Ob a) => Monoid (SP (a :: k)) where
  mempty = coarr terminate
  mappend = coarr (id &&& id)
instance (HasPullbacks k, Ob a) => Comonoid (SP (a :: k)) where
  counit = arr terminate
  comult = arr (id &&& id)
instance (HasPullbacks k, Ob a) => Frobenius (SP (a :: k)) where
  spider @x @y = spiderDefault @x @y @(SP a)
instance (HasPullbacks k) => Hypergraph (SPAN k)
instance (HasPullbacks k) => CopyDiscard (SPAN k)

instance (HasPullbacks k) => Closed (SPAN k) where
  type a ~~> b = ExpHG a b
  withObExp @(SP a) @(SP b) r = withObProd @k @a @b r
  curry @a @b = curryHG @a @b
  apply @b @c = applyHG @b @c

instance (HasPullbacks k) => StarAutonomous (SPAN k) where
  type Dual a = a
  dual (Span f g) = Span g f
  dualInv (Span f g) = Span g f
  linDist @(SP a) @(SP b) (Span f g) = Span (fst @k @a @b . f) (snd @k @a @b . f &&& g)
  linDistInv @_ @(SP b) @(SP c) (Span f g) = Span (f &&& fst @k @b @c . g) (snd @k @b @c . g)
instance (HasPullbacks k) => CompactClosed (SPAN k) where
  distribDual @(SP a) @(SP b) = withObProd @k @a @b id
  dualUnit = id

instance (HasPullbacks k) => DaggerProfunctor (Span :: CAT (SPAN k)) where
  dagger = dual
