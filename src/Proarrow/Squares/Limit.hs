{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares.Limit where

import Proarrow.Category.Bicategory (Adjunction, Bicategory (..))
import Proarrow.Category.Bicategory qualified as Adj
import Proarrow.Category.Bicategory.Strictified (Path (..), SPath (..), Strictified (..))
import Proarrow.Category.Equipment (HasCompanions (..), Sq (..), (===), (|||))
import Proarrow.Category.Equipment.Limit qualified as L
import Proarrow.Core (CategoryOf (..), obj, (//))
import Proarrow.Squares (vArr, vCombine, vId, vId', vSplit, vUnitor, vUnitorInv)

-- | The projection out of the @j@-weighted limit @l@ of @d@.
--
-- > a--l--k
-- > |  v  |
-- > j--@  |
-- > |  v  |
-- > i--d--k
limit
  :: forall {hk} {vk} {a} {i} {k} (j :: hk i a) (d :: vk i k)
   . (Ob0 vk i, L.HasLimits vk j k, Ob d)
  => Sq '(j ::: Nil, L.Limit j d ::: Nil) '(Nil, d ::: Nil)
limit =
  let l = L.limitObj @vk @j @k @d
  in Sq
      ( Str
          (SCons (obj @j) (SCons (mapCompanion @hk l) SNil))
          (SCons (mapCompanion @hk (obj @d)) SNil)
          (L.limit @vk @j @k @d)
      )
      \\\ l

-- | The universal property of the limit.
--
-- The dotted inner square is the input square, the outer square is the output square.
--
-- > a-+--p--+-k
-- > | :  v  : |
-- > | j--@  : |
-- > | :  v  : |
-- > | i..d..k |
-- > a----l----k
limitUniv
  :: forall {hk} {vk} {a} {i} {k} (j :: hk i a) (d :: vk i k) (p :: vk a k)
   . (Ob0 vk i, L.HasLimits vk j k, Ob d, Ob p)
  => Sq '(j ::: Nil, p ::: Nil) '(Nil, d ::: Nil)
  -> Sq '(Nil :: Path hk a a, p ::: Nil) '(Nil, L.Limit j d ::: Nil)
limitUniv (Sq (Str _ _ n)) = vArr (L.limitUniv @vk @j @k @d @p n) \\\ n

-- | Preservation of limits by right adjoints
--
-- Let @l@ be the @j@-weighted limit of @d and @l'@ be the @j@-weighted limit of @g ∘ d@.
-- Then we provide the following square:
--
-- > a--l'-k'
-- > |  v  |
-- > |  @  |
-- > | / \ |
-- > | v v |
-- > a-l-g-k'
--
-- With this implementation:
--
-- > +-----l'--+---------+
-- > |     v   |   /@\   |
-- > |     |   |  v   v  |
-- > +-+---l'--+-f-+-+-g-+
-- > | :   v   | v : | v |
-- > | j---@   | | : | | |
-- > | :  / \  | | : | | |
-- > | : v   v | v : | | |
-- > | +-d-+-g-+-f-+ | | |
-- > | : | | v   v : | | |
-- > | : v |  \@/  : | | |
-- > | +.d.+.......+ | v |
-- > +-------l-------+-g-+
rightAdjointPreservesLimits
  :: forall {hk} {vk} {k} {k'} {i} {a} (f :: vk k' k) (g :: vk k k') (d :: vk i k) (j :: hk i a)
   . ( Adjunction f g
     , HasCompanions hk vk
     , Ob d
     , Ob f
     , Ob g
     , L.HasLimits vk j k
     , L.HasLimits vk j k'
     , Ob0 vk i
     , Ob0 vk k
     , Ob0 vk k'
     , Ob0 vk a
     )
  => Sq '(Nil :: Path hk a a, L.Limit j (g `O` d) ::: Nil) '(Nil, L.Limit j d ::: g ::: Nil)
rightAdjointPreservesLimits =
  let g = obj @g; d = obj @d; f = obj @f
  in g `o` d //
      let l' = L.limitObj @vk @j @k' @(g `O` d)
      in vId' l' ||| unit @f @g
          === ( vCombine
                  === limitUniv @j
                    ( vSplit
                        === (limit @j === vSplit) ||| vId @f
                        === vId @d ||| counit @f @g
                    )
              )
            ||| vId @g
          \\\ l'
          \\\ f `o` l'

-- | The inverse works for any arrow:
--
-- The required square
--
-- > a-l-g-k'
-- > | v v |
-- > | \@/ |
-- > |  |  |
-- > a--l'-k'
--
-- is implemented as
--
-- > a-+-l-+-g-+-k'
-- > | : v | v : |
-- > | j-@ | | : |
-- > | : v | v : |
-- > | +.d.+.g.+ |
-- > a-----l'----k'
rightAdjointPreservesLimitsInv
  :: forall {hk} {vk} {k} {k'} {i} {a} (g :: vk k k') (d :: vk i k) (j :: hk i a)
   . (HasCompanions hk vk, Ob d, Ob g, L.HasLimits vk j k, L.HasLimits vk j k', Ob0 vk i, Ob0 vk k, Ob0 vk k', Ob0 vk a)
  => Sq '(Nil :: Path hk a a, L.Limit j d ::: g ::: Nil) '(Nil, L.Limit j (g `O` d) ::: Nil)
rightAdjointPreservesLimitsInv =
  let l = L.limitObj @vk @j @k @d; g = obj @g; d = obj @d
  in vCombine
      === limitUniv @j @(g `O` d) @(g `O` L.Limit j d)
        ( vSplit
            === limit @j @d ||| vId @g
            === vCombine
        )
      \\\ l
      \\\ g `o` d
      \\\ g `o` l

unit
  :: forall {hk} {vk} {j} {k} (f :: vk j k) (g :: vk k j)
   . (Adjunction f g, HasCompanions hk vk, Ob f, Ob g, Ob0 vk j, Ob0 vk k)
  => Sq '(Nil :: Path hk j j, Nil) '(Nil, f ::: g ::: Nil)
unit = vUnitorInv === vArr (Adj.unit @f @g) === vSplit

counit
  :: forall {hk} {vk} {j} {k} (f :: vk j k) (g :: vk k j)
   . (Adjunction f g, HasCompanions hk vk, Ob f, Ob g, Ob0 vk j, Ob0 vk k)
  => Sq '(Nil :: Path hk k k, g ::: f ::: Nil) '(Nil, Nil)
counit = vCombine === vArr (Adj.counit @f @g) === vUnitor