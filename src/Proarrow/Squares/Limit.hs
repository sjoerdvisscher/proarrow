{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares.Limit where

import Prelude (($))

import Proarrow.Category.Bicategory
  ( Adjunction
  , Bicategory (..)
  )
import Proarrow.Category.Bicategory qualified as Adj
import Proarrow.Category.Bicategory.Strictified (Path (..), Strictified (..))
import Proarrow.Category.Equipment (Equipment, IsCotight, IsTight, Tight, withObO2)
import Proarrow.Category.Equipment.Limit qualified as L
import Proarrow.Core (CategoryOf (..))
import Proarrow.Squares
  ( Sq
  , Sq' (..)
  , fromLeft
  , toRight
  , vArr
  , vCombine
  , vId
  , vSplit
  , vUnitor
  , vUnitorInv
  , (===)
  , (|||)
  )

-- | The projection out of the @j@-weighted limit @l@ of @d@.
--
-- > A--l--K
-- > |  v  |
-- > j--@  |
-- > |  v  |
-- > I--d--K
limit
  :: forall {kk} {a} {i} {k} (j :: kk i a) (d :: kk i k)
   . (L.HasLimits j k, IsTight d)
  => Sq (j ::: Nil) Nil (L.Limit j d ::: Nil) (d ::: Nil)
limit = withOb0s @kk @d $ withOb0s @kk @j $ L.withObLimit @j @k @d $ Sq $ St $ L.limit @j

-- | The universal property of the limit.
--
-- The dotted inner square is the input square, the outer square is the output square.
--
-- > A---------K
-- > | K.....K |
-- > p---\   : |
-- > | :  @->d l
-- > | j-/   : |
-- > | I.....I |
-- > A---------A
limitUniv
  :: forall {kk} {a} {i} {k} (j :: kk i a) (d :: kk i k) (p :: kk a k)
   . (L.HasLimits j k, IsTight d, Ob p)
  => Sq (j ::: p ::: Nil) (d ::: Nil) Nil Nil
  -> Sq (p ::: Nil) (L.Limit j d ::: Nil) Nil Nil
limitUniv (Sq (St n)) = withOb0s @kk @j $ L.withObLimit @j @k @d $ Sq $ St $ L.limitUniv @j n

-- |
--
-- > A-+--p--+-K
-- > | :  v  : |
-- > | j--@  : |
-- > | :  v  : |
-- > | I..d..K |
-- > A----l----K
limitUniv'
  :: forall {kk} {a} {i} {k} (j :: kk i a) (d :: kk i k) (p :: kk a k)
   . (L.HasLimits j k, IsTight d, IsTight p)
  => Sq (j ::: Nil) Nil (p ::: Nil) (d ::: Nil)
  -> Sq Nil Nil (p ::: Nil) (L.Limit j d ::: Nil)
limitUniv' n = L.withObLimit @j @k @d $ toRight ||| limitUniv @j @d @p (fromLeft === n === toRight) ||| fromLeft

-- | Preservation of limits by right adjoints
--
-- Let @l@ be the @j@-weighted limit of @d@ and @l'@ be the @j@-weighted limit of @g ∘ d@.
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
  :: forall {kk} {k} {k'} {i} {a} (f :: kk k' k) (g :: kk k k') (d :: kk i k) (j :: kk i a)
   . ( Adjunction f g
     , Equipment kk
     , IsTight d
     , IsTight f
     , IsTight g
     , L.HasLimits j k
     , L.HasLimits j k'
     )
  => Sq Nil Nil (L.Limit j (g `O` d) ::: Nil) (L.Limit j d ::: g ::: Nil)
rightAdjointPreservesLimits =
  withObO2 @Tight @_ @g @d $
    L.withObLimit @j @_ @(g `O` d) $
      withObO2 @Tight @_ @f @(L.Limit j (g `O` d)) $
        vId ||| unit @f @g
          === ( vCombine
                  === limitUniv' @j
                    ( vSplit
                        === (limit @j === vSplit) ||| vId
                        === vId @d ||| counit @f @g
                    )
              )
            ||| vId

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
  :: forall {kk} {k} {k'} {i} {a} (f :: kk k' k) (g :: kk k k') (d :: kk i k) (j :: kk i a)
   . ( Adjunction f g
     , Equipment kk
     , IsTight d
     , IsTight f
     , IsTight g
     , L.HasLimits j k
     , L.HasLimits j k'
     )
  => Sq Nil Nil (L.Limit j d ::: g ::: Nil) (L.Limit j (g `O` d) ::: Nil)
rightAdjointPreservesLimitsInv =
  L.withObLimit @j @k @d $
    withObO2 @Tight @_ @g @d $
      withObO2 @Tight @_ @g @(L.Limit j d) $
        vCombine
          === limitUniv' @j @(g `O` d) @(g `O` L.Limit j d)
            ( vSplit
                === limit @j @d ||| vId @g
                === vCombine
            )

-- | The projection into the @j@-weighted colimit @c@ of @d@.
--
-- > I-----I
-- > j-\   |
-- > |  @-<d
-- > c</   |
-- > K-----K
colimit
  :: forall {kk} {a} {i} {k} (j :: kk a i) (d :: kk k i)
   . (L.HasColimits j k, IsCotight d)
  => Sq (L.Colimit j d ::: j ::: Nil) (d ::: Nil) Nil Nil
colimit = withOb0s @kk @d $ withOb0s @kk @j $ L.withObColimit @j @k @d $ Sq $ St $ L.colimit @j

-- | The universal property of the colimit.
--
-- The dotted inner square is the input square, the outer square is the output square.
--
-- > A---------A
-- > | I.....I |
-- > | j-\   : |
-- > | :  @-<d c
-- > p---/   : |
-- > | K.....K |
-- > K---------K
colimitUniv
  :: forall {kk} {a} {i} {k} (j :: kk a i) (d :: kk k i) (p :: kk k a)
   . (L.HasColimits j k, IsCotight d, Ob p)
  => Sq (p ::: j ::: Nil) (d ::: Nil) Nil Nil
  -> Sq (p ::: Nil) (L.Colimit j d ::: Nil) Nil Nil
colimitUniv (Sq (St n)) = withOb0s @kk @j $ L.withObColimit @j @k @d $ Sq $ St $ L.colimitUniv @j @k n

-- colimitUniv'
--   :: forall {hk} {vk} {a} {i} {k} (j :: hk a i) (d :: vk i k) (p :: vk a k)
--    . (Ob0 vk i, Ob0 vk a, Ob0 vk k, L.HasColimits vk j k, Ob d, Ob p)
--   => Sq '(j ::: Nil, d ::: Nil) '(Nil, p ::: Nil)
--   -> Sq '(Nil :: Path hk a a, L.Colimit j d ::: Nil) '(Nil, p ::: Nil)
-- colimitUniv' n =
--   withObConjoint @hk @vk @p $
--     fromRight ||| (colimitUniv @j @d @(Conjoint hk p) (n === toLeft))

-- -- | Preservation of colimits by left adjoints
-- --
-- -- Let @c@ be the @j@-weighted colimit of @d@ and @c'@ be the @j@-weighted colimit of @g ∘ d@.
-- -- Then we provide the following square:
-- --
-- -- > A-c-f-K'
-- -- > | v v |
-- -- > | \ / |
-- -- > |  @  |
-- -- > |  v  |
-- -- > A--c'-K'
-- --
-- -- With this implementation:
-- --
-- -- > +-------c-------+-f-+
-- -- > | +.d.+.......+ | v |
-- -- > | : v |  /@\  : | | |
-- -- > | : | | v   v : | | |
-- -- > | +-d-+-f-+-g-+ | | |
-- -- > | : v   v | v : | | |
-- -- > | :  \ /  | | : | | |
-- -- > | j---@   | | : | | |
-- -- > | :   v   | v : | v |
-- -- > +-+---c'--+-g-+-+-f-+
-- -- > |     |   |  v   v  |
-- -- > |     v   |   \@/   |
-- -- > +-----c'--+---------+
-- leftAdjointPreservesColimits
--   :: forall {hk} {vk} {k} {k'} {i} {a} (f :: vk k k') (g :: vk k' k) (d :: vk i k) (j :: hk a i)
--    . ( Adjunction f g
--      , HasCompanions hk vk
--      , Ob d
--      , Ob f
--      , Ob g
--      , L.HasColimits vk j k
--      , L.HasColimits vk j k'
--      , Ob0 vk i
--      , Ob0 vk k
--      , Ob0 vk k'
--      , Ob0 vk a
--      )
--   => Sq '(Nil :: Path hk a a, L.Colimit j d ::: f ::: Nil) '(Nil, L.Colimit j (f `O` d) ::: Nil)
-- leftAdjointPreservesColimits =
--   withOb2 @_ @f @d $
--     L.withObColimit @vk @j @k' @(f `O` d) $
--       withOb2 @_ @g @(L.Colimit j (f `O` d)) $
--         ( colimitUniv' @j
--             ( vId @d ||| unit @f @g
--                 === (vCombine === colimit @j) ||| vId @g
--                 === vCombine
--             )
--             === vSplit
--         )
--           ||| vId @f
--           === vId @(L.Colimit j (f `O` d)) ||| counit @f @g

-- -- | The inverse works for any arrow:
-- --
-- -- The required square
-- --
-- -- > A--c'-K'
-- -- > |  |  |
-- -- > | /@\ |
-- -- > | v v |
-- -- > A-c-g-K'
-- --
-- -- is implemented as
-- --
-- -- > A-----c'----K'
-- -- > | +.d.+.f.+ |
-- -- > | : v | v : |
-- -- > | j-@ | | : |
-- -- > | : v | v : |
-- -- > A-+-c-+-f-+-K'
-- leftAdjointPreservesColimitsInv
--   :: forall {hk} {vk} {k} {k'} {i} {a} (f :: vk k k') (d :: vk i k) (j :: hk a i)
--    . (HasCompanions hk vk, Ob d, Ob f, L.HasColimits vk j k, L.HasColimits vk j k', Ob0 vk i, Ob0 vk k, Ob0 vk k', Ob0 vk a)
--   => Sq '(Nil :: Path hk a a, L.Colimit j (f `O` d) ::: Nil) '(Nil, L.Colimit j d ::: f ::: Nil)
-- leftAdjointPreservesColimitsInv =
--   L.withObColimit @vk @j @k @d $
--     withOb2 @vk @f @d $
--       withOb2 @vk @f @(L.Colimit j d) $
--         colimitUniv' @j @(f `O` d) @(f `O` L.Colimit j d)
--           ( vSplit
--               === colimit @j @d ||| vId @f
--               === vCombine
--           )
--           === vSplit

unit
  :: forall {kk} {j} {k} (f :: kk j k) (g :: kk k j)
   . (Adjunction f g, Equipment kk, IsTight f, IsTight g)
  => Sq Nil Nil Nil (f ::: g ::: Nil)
unit = withOb0s @kk @f $ withObO2 @Tight @kk @g @f $ vUnitorInv === vArr (Adj.unit @f @g) === vSplit

counit
  :: forall {kk} {j} {k} (f :: kk j k) (g :: kk k j)
   . (Adjunction f g, Equipment kk, IsTight f, IsTight g)
  => Sq Nil Nil (g ::: f ::: Nil) Nil
counit = withOb0s @kk @f $ withObO2 @Tight @kk @f @g $ vCombine === vArr (Adj.counit @f @g) === vUnitor