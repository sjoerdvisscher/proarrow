{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Enriched where

import Data.Kind (Constraint, Type)
import Prelude (Maybe (..))

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Constraint (CONSTRAINT (..), (:-) (..))
import Proarrow.Category.Instance.PointedHask (POINTED (..), Pointed (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (Any, CAT, CategoryOf (..), Kind, Profunctor (..), type (+->))
import Proarrow.Monoid (MONOIDK (..), Mon (..), Monoid (..))
import Proarrow.Object.BinaryProduct ()
import Proarrow.Object.Exponential (Closed (..), lower, mkExponential)
import Proarrow.Object.Initial (HasZeroObject (..))
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..), CodiscreteProfunctor (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Wrapped (Wrapped (..))
import qualified Proarrow.Category.Instance.Unit as U

-- | Working with enriched categories and profunctors in Haskell is hard.
-- Instead we encode them using the underlying regular category/profunctor,
-- and show that the enriched structure can be recovered.
type Enriched :: forall {j} {k}. Kind -> j +-> k -> Constraint
class (Monoidal v, Profunctor p) => Enriched v (p :: j +-> k) where
  type Hom v (p :: j +-> k) (a :: k) (b :: j) :: v
  underlying :: p a b -> Unit ~> Hom v p a b
  enriched :: (Ob a, Ob b) => Unit ~> Hom v p a b -> p a b

-- abusing SUBCAT Any as a cheap wrapper to prevent overlapping instances
type Self k = SUBCAT (Any :: k -> Constraint)

-- | Closed monoidal categories are enriched in themselves.
instance (Closed k) => Enriched (Self k) (Id :: k +-> k) where
  type Hom (Self k) (Id :: k +-> k) (a :: k) (b :: k) = SUB (a ~~> b)
  underlying (Id f) = Sub (mkExponential f)
  enriched (Sub f) = Id (lower f)

instance (Profunctor p) => Enriched Type (Wrapped p) where
  type Hom Type (Wrapped p) a b = p a b
  underlying (Wrapped p) () = p
  enriched f = Wrapped (f ())

instance (DaggerProfunctor p) => Enriched (Type, Type) (Wrapped p) where
  type Hom (Type, Type) (Wrapped p) a b = '(p a b, p b a)
  underlying (Wrapped p) = (\() -> p) :**: (\() -> dagger p)
  enriched (f :**: _) = Wrapped (f ())

instance (ThinProfunctor p) => Enriched CONSTRAINT (Wrapped p) where
  type Hom CONSTRAINT (Wrapped p) a b = CNSTRNT (HasArrow p a b)
  underlying (Wrapped p)= Entails (\r -> withArr p r)
  enriched (Entails f) = Wrapped (f arr)

instance (CodiscreteProfunctor p) => Enriched () (Wrapped p) where
  type Hom () (Wrapped p) a b = '()
  underlying _ = U.Unit
  enriched U.Unit = Wrapped anyArr

instance (HasZeroObject k) => Enriched POINTED (Id :: k +-> k) where
  type Hom POINTED (Id :: k +-> k) (a :: k) (b :: k) = P (a ~> b)
  underlying (Id f) = Pt \() -> Just f
  enriched (Pt f) = Id (case f () of Just g -> g; Nothing -> zero)

-- | A monoid is a one object enriched category.
instance (Monoid (m :: k)) => Enriched k (Mon :: CAT (MONOIDK m)) where
  type Hom k (Mon :: MONOIDK m +-> MONOIDK m) M M = m
  underlying (Mon f) = f
  enriched f = Mon f
