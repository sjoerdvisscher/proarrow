{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Weighted limits and colimits as squares. The weight is a vertical profunctor;
-- diagrams and their limits or colimits are horizontal functors.
module Proarrow.Squares.Limit where

import Proarrow.Adjunction (Adjunction)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Colimit qualified as C
import Proarrow.Core (type (+->))
import Proarrow.Limit qualified as L
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Profunctor.Instance.Composition ((:.:))
import Proarrow.Profunctor.Representable
  ( CorepStar
  , Representable
  , mapCorepStar
  , unwrapRepresentable
  , wrapRepresentable
  )
import Proarrow.Squares
  ( Sq (..)
  , fromBottom
  , fromTop
  , hArr
  , hCombine
  , hCombineCorep
  , hId
  , hSplit
  , hSplitCorep
  , mapSq
  , toBottom
  , toTop
  , (===)
  , (|||)
  )
import Proarrow.Squares.Kan (corepMateInv, corepSquare)

-- | The limiting cone, with the weight vertical and the limit and diagram horizontal.
--
-- > A-----j-----I
-- > |     |     |
-- > l>----@---->d
-- > |           |
-- > K-----------K
limit
  :: forall {i} {a} (j :: i +-> a) k (d :: i +-> k)
   . (L.HasLimits j k, Representable d)
  => Sq (j ::: Nil) Nil (L.Limit j d ::: Nil) (d ::: Nil)
limit = Sq (L.limit @j @k @d)

-- | Factor a cone through the limit.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > A-------------------A
-- > |                   |
-- > |   A.....j.....I   |
-- > |   :     |     :   |
-- > p>--------@---->d   l
-- > |   :           :   |
-- > |   K...........K   |
-- > |                   |
-- > K-------------------K
limitUniv
  :: forall {i} {a} (j :: i +-> a) k (d :: i +-> k) (p :: a +-> k)
   . (L.HasLimits j k, Representable d, Representable p)
  => Sq (j ::: Nil) Nil (p ::: Nil) (d ::: Nil)
  -> Sq Nil Nil (p ::: Nil) (L.Limit j d ::: Nil)
limitUniv = mapSq (\(Prof n) -> Prof (L.limitUniv @j @k @d n))

-- | Preservation of weighted limits by a right adjoint @p@.
-- Here @l@ is the @j@-weighted limit of @d@, and @l'@ is the limit of @p . d@.
--
-- > A-----------A
-- > |      /--->l
-- > l'>---@     |
-- > |      \--->p
-- > B-----------B
--
-- Bend the residual @p@ out of the limiting cone of @p :.: d@. Since @p@ is
-- also the conjoint of @CorepStar p@, it bends onto the left as that functor,
-- allowing 'limitUniv' to factor the cone through @l@. Bending @p@ back onto
-- the right gives the comparison above.
-- The bends use the unit and counit of @CorepStar p@ ⊣ @p@.
--
-- In the expanded composite, @f = CorepStar p@. The dotted rectangle encloses
-- the cone passed to 'limitUniv'; its factor is @l@ on the outer right boundary.
-- The three @\@@ nodes, from top to bottom, are the limiting cone of @p . d@,
-- the counit, and the unit. The pairs of bends are drawn as unit and counit
-- nodes, and combining and splitting paths is left implicit.
--
-- > A-----------------------------------A
-- > |                                   |
-- > |         A.......j...........I     |
-- > |         :       | --------->d     l
-- > |         :       |/          :     |
-- > l'>---------------@           :     |
-- > |         :        \          :     |
-- > |         :         --p       :     |
-- > |         :            \      :     |
-- > |         :             @     :     |
-- > |         :            /      :     |
-- > |       --f>-----------       :     |
-- > |      /  K...................K     |
-- > |     @                             |
-- > |      \                            |
-- > |       --------------------------->p
-- > |                                   |
-- > B-----------------------------------B
rightAdjointPreservesLimits
  :: forall {k} {k'} {i} {a} (j :: i +-> a) (p :: k +-> k') (d :: i +-> k)
   . (Adjunction p, Representable d, L.HasLimits j k, L.HasLimits j k')
  => Sq Nil Nil (L.Limit j (p :.: d) ::: Nil) (L.Limit j d ::: p ::: Nil)
rightAdjointPreservesLimits =
  (hId === fromBottom @(CorepStar p))
    ||| ( hCombine
            ||| limitUniv @j @k @d
              ( hSplit
                  ||| ( ( limit @j @k' @(p :.: d)
                            ||| hSplit
                            ||| (hId === toBottom)
                        )
                          === toTop
                      )
              )
        )
    === fromTop

-- | The inverse comparison, which exists for any representable @p@.
-- Applying @p@ to the limiting cone of @d@ gives a cone for @p :.: d@;
-- 'limitUniv' factors it through @l'@.
--
-- > A-----------A
-- > l>---\      |
-- > |     @--->l'
-- > p>---/      |
-- > B-----------B
--
-- The dotted rectangle encloses the cone obtained by applying @p@ to the
-- limiting cone of @d@. Its two right-hand functors are combined before
-- 'limitUniv' produces @l'@ on the outer boundary.
--
-- > A---------------------------A
-- > |                           |
-- > |   A.........j.........I   |
-- > |   :         |         :   |
-- > l>------------@-------->d  l'
-- > |   :                   :   |
-- > |   :                   :   |
-- > p>--------------------->p   |
-- > |   B...................B   |
-- > |                           |
-- > B---------------------------B
rightAdjointPreservesLimitsInv
  :: forall {k} {k'} {i} {a} (j :: i +-> a) (p :: k +-> k') (d :: i +-> k)
   . (Representable p, Representable d, L.HasLimits j k, L.HasLimits j k')
  => Sq Nil Nil (L.Limit j d ::: p ::: Nil) (L.Limit j (p :.: d) ::: Nil)
rightAdjointPreservesLimitsInv =
  hCombine
    ||| limitUniv @j @k' @(p :.: d)
      ( hSplit
          ||| (limit @j @k @d === hId)
          ||| hCombine
      )

-- | The colimiting cocone, expressed using the corepresenting functors.
--
-- > I-----j-----A
-- > |     |     |
-- > d>----@---->c
-- > |           |
-- > K-----------K
colimit
  :: forall {i} {a} (j :: a +-> i) k (d :: k +-> i)
   . (C.HasColimits j k, Corepresentable d)
  => Sq (j ::: Nil) Nil (CorepStar d ::: Nil) (CorepStar (C.Colimit j d) ::: Nil)
colimit = corepSquare (C.colimit @j @k @d)

-- | Factor a cocone through the colimit.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > A-------------------A
-- > |                   |
-- > |   I.....j.....A   |
-- > |   :     |     :   |
-- > c   d>----@-------->p
-- > |   :           :   |
-- > |   K...........K   |
-- > |                   |
-- > K-------------------K
colimitUniv
  :: forall {i} {a} (j :: a +-> i) k (d :: k +-> i) (p :: k +-> a)
   . (C.HasColimits j k, Corepresentable d, Corepresentable p)
  => Sq (j ::: Nil) Nil (CorepStar d ::: Nil) (CorepStar p ::: Nil)
  -> Sq Nil Nil (CorepStar (C.Colimit j d) ::: Nil) (CorepStar p ::: Nil)
colimitUniv = mapSq (\n -> mapCorepStar (Prof (C.colimitUniv @j @k @d (unProf (corepMateInv n)))))

-- | Preservation of weighted colimits by the left adjoint @f = CorepStar p@.
-- Here @c@ is the @j@-weighted colimit of @d@, and @c'@ is the colimit of @f . d@.
--
-- > A-----------A
-- > c>---\      |
-- > |     @--->c'
-- > f>---/      |
-- > B-----------B
--
-- Transpose the cocone of @f . d@ along @f@ ⊣ @p@, factor the resulting
-- cocone through @c@ with 'colimitUniv', and transpose the factor back.
--
-- The dotted rectangle encloses the cocone passed to 'colimitUniv';
-- its factor is @c@ on the outer left boundary.
-- The three @\@@ nodes are the colimiting cocone of @f . d@, the unit, and
-- the counit. Combining and splitting functor encodings is left implicit.
--
-- > A-----------------------------------A
-- > |                                   |
-- > |     I...........j.......A         |
-- > c     d>--------- |       :         |
-- > |     :          \|       :         |
-- > |     :           @--------------->c'
-- > |     :          /        :         |
-- > |     :       f--         :         |
-- > |     :      /            :         |
-- > |     :     @             :         |
-- > |     :      \            :         |
-- > |     :       ----------->p--       |
-- > |     K...................K  \      |
-- > |                             @     |
-- > |                            /      |
-- > f>---------------------------       |
-- > |                                   |
-- > B-----------------------------------B
leftAdjointPreservesColimits
  :: forall {k} {k'} {i} {a} (j :: a +-> i) (p :: k' +-> k) (d :: k +-> i)
   . (Adjunction p, Corepresentable d, C.HasColimits j k, C.HasColimits j k')
  => Sq Nil Nil (CorepStar (C.Colimit j d) ::: CorepStar p ::: Nil) (CorepStar (C.Colimit j (d :.: p)) ::: Nil)
leftAdjointPreservesColimits =
  ( ( colimitUniv @j @k @d
        ( ( (hId === fromBottom @(CorepStar p))
              ||| hCombineCorep
              ||| colimit @j @k' @(d :.: p)
              === fromTop
          )
            ||| (hId === hArr (wrapRepresentable @p))
            ||| hCombineCorep
        )
        ||| hSplitCorep
        ||| (hId === hArr (unwrapRepresentable @p))
    )
      === hId
  )
    ||| (hId === (toBottom @p === toTop @(CorepStar p)))

-- | The inverse comparison, which exists for any corepresentable @p@.
-- Applying @f = CorepStar p@ to the colimiting cocone of @d@ gives a cocone
-- for @d :.: p@; 'colimitUniv' factors it through @c'@.
--
-- > A-----------A
-- > |      /--->c
-- > c'>---@     |
-- > |      \--->f
-- > B-----------B
--
-- The dotted rectangle encloses the cocone obtained by applying @f@ to the
-- colimiting cocone of @d@. Its left-hand functors are combined before
-- 'colimitUniv' produces @c'@ on the outer boundary.
--
-- > A---------------------------A
-- > |                           |
-- > |   I.........j.........A   |
-- > |   :         |         :   |
-- > c'  d>--------@------------>c
-- > |   :                   :   |
-- > |   :                   :   |
-- > |   f>--------------------->f
-- > |   B...................B   |
-- > |                           |
-- > B---------------------------B
leftAdjointPreservesColimitsInv
  :: forall {k} {k'} {i} {a} (j :: a +-> i) (p :: k' +-> k) (d :: k +-> i)
   . (Corepresentable p, Corepresentable d, C.HasColimits j k, C.HasColimits j k')
  => Sq Nil Nil (CorepStar (C.Colimit j (d :.: p)) ::: Nil) (CorepStar (C.Colimit j d) ::: CorepStar p ::: Nil)
leftAdjointPreservesColimitsInv =
  colimitUniv @j @k' @(d :.: p)
    ( hSplitCorep
        ||| (colimit @j @k @d === hId)
        ||| hCombineCorep
    )
    ||| hSplitCorep
