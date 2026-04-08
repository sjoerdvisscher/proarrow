{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Instance.Rep where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Enriched.ThinCategory (ThinProfunctor (..), Thin)
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Profunctor.Representable (Representable (..), repObj)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Opposite (OPPOSITE (..))

type REPK j k = SUBCAT (Representable :: j +-> k -> Constraint)
type REP (f :: j +-> k) = SUB f :: REPK j k

type OpCorepresentable :: OPPOSITE (j +-> k) -> Constraint
class (Corepresentable (UN OP p)) => OpCorepresentable p
instance (Corepresentable (UN OP p)) => OpCorepresentable p
type COREPK j k = SUBCAT (OpCorepresentable :: OPPOSITE (k +-> j) -> Constraint)
type COREP (f :: k +-> j) = SUB (OP f) :: COREPK j k

class HasArrow (~>) (p % a) (q % a) => HasArrowRep p q a
instance HasArrow (~>) (p % a) (q % a) => HasArrowRep p q a
class (forall a. Ob a => HasArrowRep p q a) => HasAllArrows (p :: j +-> k) (q :: j +-> k)
instance (forall a. Ob a => HasArrowRep p q a) => HasAllArrows (p :: j +-> k) (q :: j +-> k)
instance (Thin k) => ThinProfunctor (Sub Prof :: CAT (REPK j k)) where
  type HasArrow (Sub Prof :: CAT (REPK j k)) (REP p) (REP q) = HasAllArrows p q
  arr @(REP p) @(REP q) = Sub (Prof \ @_ @b p -> tabulate (arr . index p) \\ repObj @p @b \\ repObj @q @b \\ p)
  withArr = withArr -- TODO, impossible?
  -- withArr @p @q (Sub (Prof n)) r = withArr @((~>) :: CAT k) (index (n trivialRep)) r
