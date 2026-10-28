{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Pointwise terminal objects as empty weighted limits.
module Proarrow.Squares.Terminal where

import Proarrow.Category.Instance.Zero (Absurd, VOID)
import Proarrow.Core (CategoryOf, type (+->))
import Proarrow.Limit.Terminal (HasTerminalObject)
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor)
import Proarrow.Profunctor.Representable (Rep, Representable)
import Proarrow.Squares (Sq)
import Proarrow.Squares.Limit qualified as L

-- | The pointwise terminal functor.
type Terminal :: forall j k. j +-> k
type Terminal @j @k = TerminalProfunctor

-- | The empty represented diagram.
type Diagram :: forall k. VOID +-> k
type Diagram @k = Rep (Absurd :: VOID +-> k)

-- | The empty cone, weighted by the empty functor.
--
-- > J----empty----0
-- > |      |      |
-- > T>-----@----->d
-- > |             |
-- > K-------------K
--
-- Here @T = Terminal@ and @d = Diagram@. The indexing category @0@ has no objects.
terminal
  :: forall j k
   . (CategoryOf j, HasTerminalObject k)
  => Sq (Rep (Absurd :: VOID +-> j) ::: Nil) Nil ((Terminal :: j +-> k) ::: Nil) (Diagram ::: Nil)
terminal = L.limit

-- | Factor an empty cone through the terminal functor, uniquely.
terminate
  :: forall {j} {k} (p :: j +-> k)
   . (HasTerminalObject k, Representable p)
  => Sq (Rep (Absurd :: VOID +-> j) ::: Nil) Nil (p ::: Nil) (Diagram ::: Nil)
  -> Sq Nil Nil (p ::: Nil) (Terminal ::: Nil)
terminate = L.limitUniv
