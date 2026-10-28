{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Pointwise binary coproducts as codiagonal-weighted colimits.
module Proarrow.Squares.BinaryCoproduct where

import Proarrow.Category.Instance.Coproduct (COPRODUCT, Codiag, Lft, Rgt, (:++:))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts)
import Proarrow.Core (type (+->))
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Corepresentable (Corep)
import Proarrow.Profunctor.Instance.Composition ((:.:))
import Proarrow.Profunctor.Instance.Coproduct (Sum)
import Proarrow.Profunctor.Representable
  ( CorepStar
  , Rep
  , RepCostar
  , Representable
  , unwrapRepresentable
  , wrapRepresentable
  )
import Proarrow.Squares (Sq, hArr, hReencode, (|||))
import Proarrow.Squares.Limit qualified as L

-- | A pair of functors, encoded as a corepresentable diagram.
type Diagram :: (j +-> k) -> (j +-> k) -> k +-> COPRODUCT j j
type Diagram f g = (RepCostar f :++: RepCostar g) :.: Corep Codiag

-- | The injection cocone. The vertical codiagonal weight selects either component.
--
-- > J+J-----codiag--------J
-- > |          |          |
-- > d>---------@--------->s
-- > |                     |
-- > K---------------------K
--
-- Here @d = CorepStar (Diagram f g)@ and @s = Sum f g@.
coproduct
  :: forall {j} {k} (f :: j +-> k) g
   . (HasBinaryCoproducts k, Representable f, Representable g)
  => Sq (Corep (Codiag :: COPRODUCT j j +-> j) ::: Nil) Nil (CorepStar (Diagram f g) ::: Nil) (Sum f g ::: Nil)
coproduct = L.colimit ||| hReencode

-- | Factor a cocone through the pointwise coproduct.
-- Composing 'coproduct' with the result recovers the input cocone, uniquely.
-- The dotted inner square is the input; the outer square is the factor.
--
-- > J-------------------J
-- > |                   |
-- > |  J+J.codiag...J   |
-- > |   :     |     :   |
-- > s   d>----@-------->p
-- > |   :           :   |
-- > |   K...........K   |
-- > |                   |
-- > K-------------------K
copair
  :: forall {j} {k} (f :: j +-> k) g (p :: j +-> k)
   . (HasBinaryCoproducts k, Representable f, Representable g, Representable p)
  => Sq (Corep (Codiag :: COPRODUCT j j +-> j) ::: Nil) Nil (CorepStar (Diagram f g) ::: Nil) (p ::: Nil)
  -> Sq Nil Nil (Sum f g ::: Nil) (p ::: Nil)
copair cocone = hReencode ||| L.colimitUniv (cocone ||| hArr wrapRepresentable) ||| hArr unwrapRepresentable

-- | Select the first component of the injection cocone.
lft
  :: forall {j} {k} (f :: j +-> k) g
   . (HasBinaryCoproducts k, Representable f, Representable g)
  => Sq Nil Nil (f ::: Nil) (Sum f g ::: Nil)
lft = hReencode ||| L.coconeAt @(Rep Lft) (coproduct @f @g)

-- | Select the second component of the injection cocone.
rgt
  :: forall {j} {k} (f :: j +-> k) g
   . (HasBinaryCoproducts k, Representable f, Representable g)
  => Sq Nil Nil (g ::: Nil) (Sum f g ::: Nil)
rgt = hReencode ||| L.coconeAt @(Rep Rgt) (coproduct @f @g)
