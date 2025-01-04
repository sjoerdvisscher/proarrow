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
-- > A--l--K
-- > |  v  |
-- > j--@  |
-- > |  v  |
-- > I--d--K
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
-- > A-+--p--+-K
-- > | :  v  : |
-- > | j--@  : |
-- > | :  v  : |
-- > | I..d..K |
-- > A----l----K
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
-- > A--l'-K'
-- > |  v  |
-- > |  @  |
-- > | / \ |
-- > | v v |
-- > A-l-g-K'
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
-- > A-l-g-K'
-- > | v v |
-- > | \@/ |
-- > |  |  |
-- > A--l'-K'
--
-- is implemented as
--
-- > A-+-l-+-g-+-K'
-- > | : v | v : |
-- > | j-@ | | : |
-- > | : v | v : |
-- > | +.d.+.g.+ |
-- > A-----l'----K'
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

-- | The projection into the @j@-weighted colimit @c@ of @d@.
--
-- > I--d--K
-- > |  v  |
-- > j--@  |
-- > |  v  |
-- > A--l--K
colimit
  :: forall {hk} {vk} {a} {i} {k} (j :: hk a i) (d :: vk i k)
   . (Ob0 vk i, L.HasColimits vk j k, Ob d)
  => Sq '(j ::: Nil, d ::: Nil) '(Nil, L.Colimit j d ::: Nil)
colimit =
  let c = L.colimitObj @vk @j @k @d
  in Sq
      ( Str
          (SCons (obj @j) (SCons (mapCompanion @hk (obj @d)) SNil))
          (SCons (mapCompanion @hk c) SNil)
          (L.colimit @vk @j @k @d)
      )
      \\\ c

-- | The universal property of the colimit.
--
-- The dotted inner square is the input square, the outer square is the output square.
--
-- > A----c----K
-- > | I..d..K |
-- > | :  v  : |
-- > | j--@  : |
-- > | :  v  : |
-- > A-+--p--+-K
colimitUniv
  :: forall {hk} {vk} {a} {i} {k} (j :: hk a i) (d :: vk i k) (p :: vk a k)
   . (Ob0 vk i, L.HasColimits vk j k, Ob d, Ob p)
  => Sq '(j ::: Nil, d ::: Nil) '(Nil, p ::: Nil)
  -> Sq '(Nil :: Path hk a a, L.Colimit j d ::: Nil) '(Nil, p ::: Nil)
colimitUniv (Sq (Str _ _ n)) = vArr (L.colimitUniv @vk @j @k @d @p n) \\\ n

-- | Preservation of colimits by left adjoints
--
-- Let @c@ be the @j@-weighted colimit of @d@ and @c'@ be the @j@-weighted colimit of @g ∘ d@.
-- Then we provide the following square:
--
-- > A-c-f-K'
-- > | v v |
-- > | \ / |
-- > |  @  |
-- > |  v  |
-- > A--c'-K'
--
-- With this implementation:
--
-- > +-------c-------+-f-+
-- > | +.d.+.......+ | v |
-- > | : v |  /@\  : | | |
-- > | : | | v   v : | | |
-- > | +-d-+-f-+-g-+ | | |
-- > | : v   v | v : | | |
-- > | :  \ /  | | : | | |
-- > | j---@   | | : | | |
-- > | :   v   | v : | v |
-- > +-+---c'--+-g-+-+-f-+
-- > |     |   |  v   v  |
-- > |     v   |   \@/   |
-- > +-----c'--+---------+
leftAdjointPreservesColimits
  :: forall {hk} {vk} {k} {k'} {i} {a} (f :: vk k k') (g :: vk k' k) (d :: vk i k) (j :: hk a i)
   . ( Adjunction f g
     , HasCompanions hk vk
     , Ob d
     , Ob f
     , Ob g
     , L.HasColimits vk j k
     , L.HasColimits vk j k'
     , Ob0 vk i
     , Ob0 vk k
     , Ob0 vk k'
     , Ob0 vk a
     )
  => Sq '(Nil :: Path hk a a, L.Colimit j d ::: f ::: Nil) '(Nil, L.Colimit j (f `O` d) ::: Nil)
leftAdjointPreservesColimits =
  let f = obj @f; g = obj @g; d = obj @d
  in f `o` d //
      let c' = L.colimitObj @vk @j @k' @(f `O` d)
      in ( colimitUniv @j
            ( vId @d ||| unit @f @g
                === (vCombine === colimit @j) ||| vId @g
                === vCombine
            )
            === vSplit
         )
          ||| vId @f
          === vId' c' ||| counit @f @g
          \\\ c'
          \\\ g `o` c'

-- | The inverse works for any arrow:
--
-- The required square
--
-- > A--c'-K'
-- > |  |  |
-- > | /@\ |
-- > | v v |
-- > A-c-g-K'
--
-- is implemented as
--
-- > A-----c'----K'
-- > | +.d.+.f.+ |
-- > | : v | v : |
-- > | j-@ | | : |
-- > | : v | v : |
-- > A-+-c-+-f-+-K'
leftAdjointPreservesColimitsInv
  :: forall {hk} {vk} {k} {k'} {i} {a} (f :: vk k k') (d :: vk i k) (j :: hk a i)
   . (HasCompanions hk vk, Ob d, Ob f, L.HasColimits vk j k, L.HasColimits vk j k', Ob0 vk i, Ob0 vk k, Ob0 vk k', Ob0 vk a)
  => Sq '(Nil :: Path hk a a, L.Colimit j (f `O` d) ::: Nil) '(Nil, L.Colimit j d ::: f ::: Nil)
leftAdjointPreservesColimitsInv =
  let c = L.colimitObj @vk @j @k @d; f = obj @f; d = obj @d
  in colimitUniv @j @(f `O` d) @(f `O` L.Colimit j d)
        ( vSplit
            === colimit @j @d ||| vId @f
            === vCombine
        )
      === vSplit
      \\\ c
      \\\ f `o` d
      \\\ f `o` c

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