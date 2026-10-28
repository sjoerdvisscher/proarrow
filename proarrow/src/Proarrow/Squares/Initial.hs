{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Pointwise initial objects as empty weighted colimits.
module Proarrow.Squares.Initial where

import Proarrow.Category.Instance.Zero (Absurd, VOID)
import Proarrow.Colimit.Initial (HasInitialObject)
import Proarrow.Core (CategoryOf, type (+->))
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Corepresentable (Corep)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Representable (CorepStar, Representable, unwrapRepresentable, wrapRepresentable)
import Proarrow.Squares (Sq, hArr, (|||))
import Proarrow.Squares.Limit qualified as L

-- | The pointwise initial functor.
type Initial :: forall j k. j +-> k
type Initial @j @k = CorepStar (TerminalProfunctor :: k +-> j)

-- | The empty corepresentable diagram.
type Diagram :: forall k. k +-> VOID
type Diagram @k = Corep (Absurd :: VOID +-> k)

-- | The empty cocone, weighted by the empty functor.
--
-- > 0----empty----J
-- > |      |      |
-- > d>-----@----->I
-- > |             |
-- > K-------------K
--
-- Here @I = Initial@ and @d = CorepStar Diagram@. The indexing category @0@ has no objects.
initial
  :: forall j k
   . (CategoryOf j, HasInitialObject k)
  => Sq (Corep (Absurd :: VOID +-> j) ::: Nil) Nil (CorepStar (Diagram :: k +-> VOID) ::: Nil) (Initial ::: Nil)
initial = L.colimit

-- | Factor an empty cocone through the initial functor, uniquely.
initiate
  :: forall {j} {k} (p :: j +-> k)
   . (HasInitialObject k, Representable p)
  => Sq (Corep (Absurd :: VOID +-> j) ::: Nil) Nil (CorepStar (Diagram :: k +-> VOID) ::: Nil) (p ::: Nil)
  -> Sq Nil Nil (Initial ::: Nil) (p ::: Nil)
initiate cocone = L.colimitUniv (cocone ||| hArr wrapRepresentable) ||| hArr unwrapRepresentable
