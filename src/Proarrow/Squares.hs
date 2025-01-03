{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares where

import Proarrow.Category.Bicategory (Bicategory (..), Ob')
import Proarrow.Category.Bicategory.Strictified (Path (..), SPath (..), Strictified (..), singleton, type (+++))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..))
import Proarrow.Category.Equipment qualified as E
import Proarrow.Core (CategoryOf (..), Promonad ((.)), obj, Obj, (\\))

infixl 6 |||
infixl 5 ===

-- | The empty square for an object.
--
-- > k-----k
-- > |     |
-- > |     |
-- > |     |
-- > k-----k
object :: (HasCompanions hk vk, Ob0 vk k) => Sq '(Nil :: Path hk k k, Nil :: Path vk k k) '(Nil, Nil)
object = E.object

-- | Make a square from a horizontal proarrow
--
-- > k-----k
-- > |     |
-- > p--@--q
-- > |     |
-- > j-----j
hArr
  :: forall {hk} {vk} {j} {k} (p :: hk j k) q
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => p ~> q
  -> Sq '(p ::: Nil, Nil :: Path vk k k) '(q ::: Nil, Nil :: Path vk j j)
hArr = E.hArr . singleton

-- | A horizontal identity square.
--
-- > j-----j
-- > |     |
-- > p-----p
-- > |     |
-- > k-----k
hId
  :: (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (p :: hk k j)) => Sq '(p ::: Nil, Nil :: Path vk j j) '(p ::: Nil, Nil)
hId = E.hId

-- | A horizontal identity square for a companion.
--
-- Requires a type application: @compId \@f@
--
-- > k-----k
-- > |     |
-- > f>--->f
-- > |     |
-- > j-----j
compId
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob0 hk j, Ob0 hk k, Ob (f :: vk j k))
  => Sq '(Companion hk f ::: Nil, Nil :: Path vk k k) '(Companion hk f ::: Nil, Nil :: Path vk j j)
compId = E.compId @(f ::: Nil)

-- | A horizontal identity square for a conjoint.
--
-- Requires a type application: @conjId \@f@
--
-- > j-----j
-- > |     |
-- > f>--->f
-- > |     |
-- > k-----k
conjId
  :: forall {hk} {vk} {j} {k} f
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk f ::: Nil, Nil :: Path vk j j) '(Conjoint hk f ::: Nil, Nil :: Path vk k k)
conjId = E.conjId @(f ::: Nil)

-- | Make a square from a vertical arrow
--
-- > j--f--k
-- > |  v  |
-- > |  @  |
-- > |  v  |
-- > j--g--k
vArr
  :: forall {hk} {vk} {j} {k} (f :: vk j k) g
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => f ~> g
  -> Sq '(Nil :: Path hk j j, f ::: Nil) '(I :: Path hk k k, g ::: Nil)
vArr = E.vArr . singleton

-- | A vertical identity square.
--
-- > j--f--k
-- > |  v  |
-- > |  |  |
-- > |  v  |
-- > j--f--k
vId
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Nil :: Path hk j j, f ::: Nil) '(Nil :: Path hk k k, f ::: Nil)
vId = E.vId

vId'
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => Obj f -> Sq '(Nil :: Path hk j j, f ::: Nil) '(Nil :: Path hk k k, f ::: Nil)
vId' f = vId \\ f

-- | Horizontal composition
--
-- > l--d--h     h--f--i     l-d+f-i
-- > |  v  |     |  v  |     |  v  |
-- > p--@--q ||| q--@--r  =  p--@--r
-- > |  v  |     |  v  |     |  v  |
-- > m--e--j     j--g--k     m-e+g-k
(|||)
  :: forall {hk} {vk} {h} {l} {m} (ps :: Path hk m l) qs rs (ds :: Path vk l h) es fs gs
   . (HasCompanions hk vk)
  => Sq '(ps, ds) '(qs, es)
  -> Sq '(qs, fs) '(rs, gs)
  -> Sq '(ps, ds +++ fs) '(rs, es +++ gs)
(|||) = (E.|||)

-- | Vertical composition
--
-- >  h--e--i
-- >  |  v  |
-- >  r--@--s
-- >  |  v  |
-- >  j--f--k
-- >    ===
-- >  j--f--k
-- >  |  v  |
-- >  p--@--q
-- >  |  v  |
-- >  l--g--m
-- >
-- >    v v
-- >
-- >  h--e--i
-- >  |  v  |
-- > p+r-@-q+s
-- >  |  v  |
-- >  j--g--k
(===)
  :: forall {hk} {vk} {h} {i} {j} {l} (ps :: Path hk l j) qs rs ss (es :: Path vk h i) fs gs
   . (HasCompanions hk vk)
  => Sq '(rs, es) '(ss, fs)
  -> Sq '(ps, fs) '(qs, gs)
  -> Sq '(ps +++ rs, es) '(qs +++ ss, gs)
(===) = (E.===)

-- | Bend a vertical arrow in the companion direction.
--
-- > j--f--k
-- > |  v  |
-- > |  \->f
-- > |     |
-- > j-----j
toRight
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob' (f :: vk j k))
  => Sq '(Nil, f ::: Nil) '(Companion hk f ::: Nil, Nil)
toRight = E.toRight

-- | Bend a vertical arrow in the conjoint direction.
--
-- > j--f--k
-- > |  v  |
-- > f<-/  |
-- > |     |
-- > k-----k
toLeft
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk f ::: Nil, f ::: Nil) '(Nil, Nil)
toLeft = E.toLeft

-- | Bend a companion proarrow back to a vertical arrow.
--
-- > k-----k
-- > |     |
-- > f>-\  |
-- > |  v  |
-- > j--f--k
fromLeft
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob' (f :: vk j k))
  => Sq '(Companion hk f ::: Nil, Nil) '(Nil, f ::: Nil)
fromLeft = E.fromLeft

-- | Bend a conjoint proarrow back to a vertical arrow.
--
-- > j-----j
-- > |     |
-- > |  /-<f
-- > |  v  |
-- > j--f--k
fromRight
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob f)
  => Sq '(Nil, Nil) '(Conjoint hk f ::: Nil, f ::: Nil)
fromRight = E.fromRight

-- -- > k--------k
-- -- > |        |
-- -- > g>----\  |
-- -- > |     |  |
-- -- > f>-\  |  |
-- -- > |  v  v  |
-- -- > i--f--g--k
-- fromLeft2
--   :: forall {hk} {vk} {i} {j} {k} (f :: vk i j) (g :: vk j k)
--    . (Equipment hk vk, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob f, Ob g)
--   => Sq '(Companion hk f ::: Companion hk g ::: Nil, Nil) '(Nil, f ::: g ::: Nil)
-- fromLeft2 =
--   fromLeft
--     === fromLeft ||| vId

-- > k--I--k
-- > |  v  |
-- > |  @  |
-- > |     |
-- > k-----k
vUnitor :: forall hk vk k. (HasCompanions hk vk, Ob0 vk k) => Sq '(Nil :: Path hk k k, I ::: Nil) '(Nil :: Path hk k k, Nil :: Path vk k k)
vUnitor = Sq (Str (SCons (mapCompanion @hk iObj) SNil) SNil compToId) \\\ iObj @vk @k

-- > k-----k
-- > |     |
-- > |  @  |
-- > |  v  |
-- > k--I--k
vUnitorInv :: forall hk vk k. (HasCompanions hk vk, Ob0 vk k) => Sq '(Nil :: Path hk k k, Nil :: Path vk k k) '(Nil :: Path hk k k, I ::: Nil)
vUnitorInv = Sq (Str SNil (SCons (mapCompanion @hk iObj) SNil) compFromId) \\\ iObj @vk @k

-- > i-f-g-k
-- > | v v |
-- > | \@/ |
-- > |  v  |
-- > i-gof-k
vCombine
  :: forall {hk} {vk} {i} {j} {k} (f :: vk i j) (g :: vk j k)
   . (HasCompanions hk vk, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob0 hk i, Ob0 hk j, Ob0 hk k, Ob f, Ob g)
  => Sq '(Nil :: Path hk i i, f ::: g ::: Nil) '(Nil, g `O` f ::: Nil)
vCombine =
  let f = obj @f; g = obj @g
  in Sq
      ( Str
          (SCons (mapCompanion @hk f) (SCons (mapCompanion @hk g) SNil))
          (SCons (mapCompanion @hk (g `o` f)) SNil)
          (compFromCompose g f)
      )
      \\\ (g `o` f)

-- > i-gof-k
-- > |  v  |
-- > | /@\ |
-- > | v v |
-- > i-f-g-k
vSplit
  :: forall {hk} {vk} {i} {j} {k} (f :: vk i j) (g :: vk j k)
   . (HasCompanions hk vk, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob0 hk i, Ob0 hk j, Ob0 hk k, Ob f, Ob g)
  => Sq '(Nil :: Path hk i i, g `O` f ::: Nil) '(Nil, f ::: g ::: Nil)
vSplit =
  let f = obj @f; g = obj @g
  in Sq
      ( Str
          (SCons (mapCompanion @hk (g `o` f)) SNil)
          (SCons (mapCompanion @hk f) (SCons (mapCompanion @hk g) SNil))
          (compToCompose g f)
      )
      \\\ (g `o` f)
