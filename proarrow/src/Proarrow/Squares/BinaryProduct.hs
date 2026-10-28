{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Pointwise binary products as codiagonal-weighted limits.
module Proarrow.Squares.BinaryProduct where

import Proarrow.Category.Instance.Coproduct (COPRODUCT, Codiag, Lft, Rgt, (:++:))
import Proarrow.Core (type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts)
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Instance.Composition ((:.:))
import Proarrow.Profunctor.Instance.Product ((:*:))
import Proarrow.Profunctor.Representable (Rep, Representable)
import Proarrow.Squares (Sq, hReencode, (|||))
import Proarrow.Squares.Limit qualified as L

-- | A pair of functors, viewed as one diagram on the disjoint union of their domains.
type Diagram :: (j +-> k) -> (j +-> k) -> COPRODUCT j j +-> k
type Diagram f g = Rep Codiag :.: (f :++: g)

-- | The projection cone. The vertical codiagonal weight selects either component.
--
-- > J-------codiag-------J+J
-- > |          |          |
-- > f*g>-------@--------->d
-- > |                     |
-- > K---------------------K
--
-- Here @d = Diagram f g@ and @f*g@ is the pointwise product.
product
  :: forall {j} {k} (f :: j +-> k) g
   . (HasBinaryProducts k, Representable f, Representable g)
  => Sq (Rep (Codiag :: COPRODUCT j j +-> j) ::: Nil) Nil (f :*: g ::: Nil) (Diagram f g ::: Nil)
product = hReencode ||| L.limit

-- | Factor a cone through the pointwise product.
-- Composing the result with 'product' recovers the input cone, uniquely.
-- The dotted inner square is the input; the outer square is the factor.
--
-- > J-------------------J
-- > |                   |
-- > |   J..codiag..J+J  |
-- > |   :     |     :   |
-- > p>--------@---->d  f*g
-- > |   :           :   |
-- > |   K...........K   |
-- > |                   |
-- > K-------------------K
pair
  :: forall {j} {k} (f :: j +-> k) g (p :: j +-> k)
   . (HasBinaryProducts k, Representable f, Representable g, Representable p)
  => Sq (Rep (Codiag :: COPRODUCT j j +-> j) ::: Nil) Nil (p ::: Nil) (Diagram f g ::: Nil)
  -> Sq Nil Nil (p ::: Nil) (f :*: g ::: Nil)
pair cone = L.limitUniv cone ||| hReencode

-- | Select the first component of the projection cone.
fst
  :: forall {j} {k} (f :: j +-> k) g
   . (HasBinaryProducts k, Representable f, Representable g)
  => Sq Nil Nil (f :*: g ::: Nil) (f ::: Nil)
fst = L.coneAt @(Rep Lft) (product @f @g) ||| hReencode

-- | Select the second component of the projection cone.
snd
  :: forall {j} {k} (f :: j +-> k) g
   . (HasBinaryProducts k, Representable f, Representable g)
  => Sq Nil Nil (f :*: g ::: Nil) (g ::: Nil)
snd = L.coneAt @(Rep Rgt) (product @f @g) ||| hReencode
