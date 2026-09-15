{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Totally ordered, integral quantales, as far as computing closures of enriched profunctors
-- needs them: 'Proarrow.Category.Instance.Bool.BOOL' (relations, reachability) and
-- 'Proarrow.Category.Instance.Cost.COST' (metric spaces, shortest paths). Besides the structure
-- their classes already provide, the closure needs a handful of facts reflected to the value level,
-- collected in 'Quantale'.
module Proarrow.Category.Enriched.Quantale where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Type.Ord (OrderingI (..))
import GHC.TypeNats (cmpNat)
import Prelude (error, type (~))

import Proarrow.Category.Enriched.Thin (Decidable, Decision (..), decide)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Cost (COST (..), GTE (..), IsCost (..), SCost (..))
import Proarrow.Category.Monoidal (Monoidal (..), leftUnitorWith, rightUnitorWith)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Hom, Promonad (..), obj)
import Proarrow.Limit.Terminal (HasTerminalObject (..), Semicartesian)

-- | As much of a quantale as a closure needs, and a totally ordered, integral one at that: a
-- 'Semicartesian' 'Distributive' category, so that the unit is the top element and the bottom
-- absorbs, in which the join of two objects is one of them ('minIs') and the order is decidable.
-- Totality is what makes a single best walk exist; in a quantale of, say, sets of paths, a join is
-- attained by no one summand. Infinite joins are not needed, since there are finitely many objects.
--
-- The methods reflect to the value level facts that GHC cannot see through the type families:
-- 'minIs' is totality, and 'unitIsNotBottom' and 'unitIsTop' say the order is nondegenerate and
-- skeletal -- the latter is antisymmetry at the unit, since 'Semicartesian' already gives the
-- arrow the other way.
class (Semicartesian v, Distributive v, Decidable v) => Quantale v where
  minIs :: forall (x :: v) y. (Ob x, Ob y) => MinIs x y
  unitIsNotBottom :: forall r. (Unit :: v) ~> InitialObject -> r
  unitIsTop :: forall (w :: v) r. (Ob w) => (Unit ~> w) -> ((w ~ Unit) => r) -> r

-- | Which of two objects their join is.
type MinIs :: forall {v}. v -> v -> Type
data MinIs x y where
  MinLeft :: ((x || y) ~ x) => MinIs x y
  MinRight :: ((x || y) ~ y) => MinIs x y

-- | In an integral quantale a tensor lies below each of its factors, since the other factor is at
-- most the unit, so a unit into a tensor is a unit into each factor.
splitUnit :: forall {v} (x :: v) y. (Quantale v, Ob x, Ob y) => Unit ~> (x ** y) -> (Unit ~> x, Unit ~> y)
splitUnit f = (rightUnitorWith @x (terminate @v @y) . f, leftUnitorWith @y (terminate @v @x) . f)

-- | The bottom absorbs the tensor, and nothing lies below the bottom.
bottomTensor :: forall {v} (x :: v) y. (Quantale v, Ob x, Ob y) => (InitialObject ** x) ~> y
bottomTensor = initiate @v @y . absorbR @v @x

-- | The arrow between two objects of a decidable order, when the caller knows it exists but its
-- existence is not derived structurally -- the triangle inequality for closures, for instance. As
-- elsewhere in "Proarrow.Category.Instance.Cost", it is checked at runtime.
checkedArrow :: forall v (x :: v) y. (Decidable v, Ob x, Ob y) => x ~> y
checkedArrow = case decide @(Hom v) @x @y of
  Yes f -> f
  No -> error "checkedArrow: the checked arrow does not exist"

-- | The walking arrow: the tensor is conjunction, the join disjunction.
instance Quantale BOOL where
  minIs @x = case obj @x of
    Tru -> MinLeft
    Fls -> MinRight
  unitIsNotBottom = \case {}
  unitIsTop Tru r = r

-- | Costs: the tensor is addition, the join the minimum. Distances are compared with 'cmpNat', whose
-- evidence makes the type-level 'Data.Type.Ord.Min' reduce; that a natural below @0@ is @0@ is
-- arithmetic GHC cannot see, so it is checked at runtime.
instance Quantale COST where
  minIs @x @y = case (sing @x, sing @y) of
    (SINF, _) -> MinRight
    (SC, SINF) -> MinLeft
    (SC @m, SC @m') -> case cmpNat (Proxy @m) (Proxy @m') of
      LTI -> MinLeft
      EQI -> MinLeft
      GTI -> MinRight
  unitIsNotBottom = \case {}
  unitIsTop @w f r = case sing @w of
    SINF -> case f of {}
    SC @m -> case f of
      GTE -> case cmpNat (Proxy @m) (Proxy @0) of
        EQI -> r
        LTI -> error "COST: a natural below 0"
