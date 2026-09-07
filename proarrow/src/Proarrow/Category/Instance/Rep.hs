{-# OPTIONS_GHC -Wno-orphans #-}

-- | Categories of __representable profunctors__: @'REPK' j k@ is the full subcategory of the
-- profunctor category on the 'Representable' profunctors, and @'COREPK' j k@ its counterpart of
-- (opposed) corepresentable ones. A representable profunctor is a functor in profunctor clothing,
-- so these play the role of functor categories between arbitrary kinds.
module Proarrow.Category.Instance.Rep where

import Data.Kind (Constraint)
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Profunctor.Representable (Representable (..), repObj)

type REPK j k = SUBCAT (Representable :: j +-> k -> Constraint)
type REP (f :: j +-> k) = SUB f :: REPK j k

type OpCorepresentable :: OPPOSITE (j +-> k) -> Constraint
class (Corepresentable (UN OP p)) => OpCorepresentable p
instance (Corepresentable (UN OP p)) => OpCorepresentable p
type COREPK j k = SUBCAT (OpCorepresentable :: OPPOSITE (k +-> j) -> Constraint)
type COREP (f :: k +-> j) = SUB (OP f) :: COREPK j k

class (HasArrow (~>) (p % a) (q % a)) => HasArrowRep p q a
instance (HasArrow (~>) (p % a) (q % a)) => HasArrowRep p q a
class (forall a. (Ob a) => HasArrowRep p q a) => HasAllArrows (p :: j +-> k) (q :: j +-> k)
instance (forall a. (Ob a) => HasArrowRep p q a) => HasAllArrows (p :: j +-> k) (q :: j +-> k)
instance (Thin k) => ThinProfunctor (Sub Prof :: CAT (REPK j k)) where
  type HasArrow (Sub Prof :: CAT (REPK j k)) (REP p) (REP q) = HasAllArrows p q
  arr @(REP p) @(REP q) = Sub (Prof \ @_ @b p -> tabulate (arr . index p) \\ repObj @p @b \\ repObj @q @b \\ p)

  -- Recovering @HasAllArrows p q@ from a natural transformation would require building the
  -- quantified @forall a. Ob a => HasArrowRep p q a@ dictionary out of per-@a@ 'withArr' calls
  -- (e.g. @withArr (index (n repUniv))@, which only proves it for one @a@) -- value-level
  -- entailment GHC cannot express (cf. GHC issue #16502). 'arr' works; 'withArr' cannot.
  withArr _ _ = P.error "withArr @(Sub Prof): cannot construct the quantified HasAllArrows dictionary (GHC #16502)"
