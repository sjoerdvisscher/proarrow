{-# OPTIONS_GHC -Wno-orphans #-}

-- | Categories of __representable profunctors__: @'REPK' j k@ is the full subcategory of the
-- profunctor category on the 'Representable' profunctors, and @'COREPK' j k@ its counterpart of
-- (opposed) corepresentable ones. A representable profunctor is a functor in profunctor clothing,
-- so these play the role of functor categories between arbitrary kinds.
module Proarrow.Category.Instance.Rep where

import Data.Kind (Constraint)

import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, type (+->))
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

-- | The natural transformation @p ':~>' q@ obtained from a thin arrow @p % a '~>' q % a@ at every
-- object, i.e. the 'Proarrow.Category.Enriched.Thin.arr' of a thin structure on @'REPK' j k@.
--
-- It is no @'Proarrow.Category.Enriched.Thin.ThinProfunctor' ('Sub' 'Prof')@ instance, because the
-- converse 'Proarrow.Category.Enriched.Thin.withArr' would have to build the quantified
-- @'HasAllArrows' p q@ from per-@a@ evidence, which GHC cannot (cf. GHC issue #16502).
repArr
  :: forall {j} {k} (p :: j +-> k) q
   . (Thin k, Ob (REP p), Ob (REP q), HasAllArrows p q)
  => REP p ~> REP q
repArr = Sub (Prof \ @_ @b p -> tabulate (arr . index p) \\ repObj @p @b \\ repObj @q @b \\ p)
