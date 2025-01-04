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
-- > K-----K
-- > |     |
-- > |     |
-- > |     |
-- > K-----K
object :: (HasCompanions hk vk, Ob0 vk k) => Sq '(Nil :: Path hk k k, Nil :: Path vk k k) '(Nil, Nil)
object = E.object

-- | Make a square from a horizontal proarrow
--
-- > K-----K
-- > |     |
-- > p--@--q
-- > |     |
-- > J-----J
hArr
  :: forall {hk} {vk} {j} {k} (p :: hk j k) q
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => p ~> q
  -> Sq '(p ::: Nil, Nil :: Path vk k k) '(q ::: Nil, Nil :: Path vk j j)
hArr = E.hArr . singleton

-- | A horizontal identity square.
--
-- > J-----J
-- > |     |
-- > p-----p
-- > |     |
-- > K-----K
hId
  :: (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (p :: hk k j)) => Sq '(p ::: Nil, Nil :: Path vk j j) '(p ::: Nil, Nil)
hId = E.hId

-- | A horizontal identity square for a companion.
--
-- Requires a type application: @compId \@f@
--
-- > K-----K
-- > |     |
-- > f>--->f
-- > |     |
-- > J-----J
compId
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob0 hk j, Ob0 hk k, Ob (f :: vk j k))
  => Sq '(Companion hk f ::: Nil, Nil :: Path vk k k) '(Companion hk f ::: Nil, Nil :: Path vk j j)
compId = E.compId @(f ::: Nil)

-- | A horizontal identity square for a conjoint.
--
-- Requires a type application: @conjId \@f@
--
-- > J-----J
-- > |     |
-- > f>--->f
-- > |     |
-- > K-----K
conjId
  :: forall {hk} {vk} {j} {k} f
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk f ::: Nil, Nil :: Path vk j j) '(Conjoint hk f ::: Nil, Nil :: Path vk k k)
conjId = E.conjId @(f ::: Nil)

-- | Make a square from a vertical arrow
--
-- > J--f--K
-- > |  v  |
-- > |  @  |
-- > |  v  |
-- > J--g--K
vArr
  :: forall {hk} {vk} {j} {k} (f :: vk j k) g
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => f ~> g
  -> Sq '(Nil :: Path hk j j, f ::: Nil) '(I :: Path hk k k, g ::: Nil)
vArr = E.vArr . singleton

-- | A vertical identity square.
--
-- > J--f--K
-- > |  v  |
-- > |  |  |
-- > |  v  |
-- > J--f--K
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
-- > L--d--H     H--f--I     L-d+f-I
-- > |  v  |     |  v  |     |  v  |
-- > p--@--q ||| q--@--r  =  p--@--r
-- > |  v  |     |  v  |     |  v  |
-- > M--e--J     J--g--K     M-e+g-K
(|||)
  :: forall {hk} {vk} {h} {l} {m} (ps :: Path hk m l) qs rs (ds :: Path vk l h) es fs gs
   . (HasCompanions hk vk)
  => Sq '(ps, ds) '(qs, es)
  -> Sq '(qs, fs) '(rs, gs)
  -> Sq '(ps, ds +++ fs) '(rs, es +++ gs)
(|||) = (E.|||)

-- | Vertical composition
--
-- >  H--e--I
-- >  |  v  |
-- >  r--@--s
-- >  |  v  |
-- >  J--f--K
-- >    ===
-- >  J--f--K
-- >  |  v  |
-- >  p--@--q
-- >  |  v  |
-- >  L--g--M
-- >
-- >    v v
-- >
-- >  H--e--I
-- >  |  v  |
-- > p+r-@-q+s
-- >  |  v  |
-- >  J--g--K
(===)
  :: forall {hk} {vk} {h} {i} {j} {l} (ps :: Path hk l j) qs rs ss (es :: Path vk h i) fs gs
   . (HasCompanions hk vk)
  => Sq '(rs, es) '(ss, fs)
  -> Sq '(ps, fs) '(qs, gs)
  -> Sq '(ps +++ rs, es) '(qs +++ ss, gs)
(===) = (E.===)

-- | Bend a vertical arrow in the companion direction.
--
-- > J--f--K
-- > |  v  |
-- > |  \->f
-- > |     |
-- > J-----J
toRight
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob' (f :: vk j k))
  => Sq '(Nil, f ::: Nil) '(Companion hk f ::: Nil, Nil)
toRight = E.toRight

-- | Bend a vertical arrow in the conjoint direction.
--
-- > J--f--K
-- > |  v  |
-- > f<-/  |
-- > |     |
-- > K-----K
toLeft
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk f ::: Nil, f ::: Nil) '(Nil, Nil)
toLeft = E.toLeft

-- | Bend a companion proarrow back to a vertical arrow.
--
-- > K-----K
-- > |     |
-- > f>-\  |
-- > |  v  |
-- > J--f--K
fromLeft
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob' (f :: vk j k))
  => Sq '(Companion hk f ::: Nil, Nil) '(Nil, f ::: Nil)
fromLeft = E.fromLeft

-- | Bend a conjoint proarrow back to a vertical arrow.
--
-- > J-----J
-- > |     |
-- > |  /-<f
-- > |  v  |
-- > J--f--K
fromRight
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob f)
  => Sq '(Nil, Nil) '(Conjoint hk f ::: Nil, f ::: Nil)
fromRight = E.fromRight

-- -- > K--------K
-- -- > |        |
-- -- > g>----\  |
-- -- > |     |  |
-- -- > f>-\  |  |
-- -- > |  v  v  |
-- -- > I--f--g--K
-- fromLeft2
--   :: forall {hk} {vk} {i} {j} {k} (f :: vk i j) (g :: vk j k)
--    . (Equipment hk vk, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob f, Ob g)
--   => Sq '(Companion hk f ::: Companion hk g ::: Nil, Nil) '(Nil, f ::: g ::: Nil)
-- fromLeft2 =
--   fromLeft
--     === fromLeft ||| vId

-- > K--I--K
-- > |  v  |
-- > |  @  |
-- > |     |
-- > K-----K
vUnitor :: forall hk vk k. (HasCompanions hk vk, Ob0 vk k) => Sq '(Nil :: Path hk k k, I ::: Nil) '(Nil :: Path hk k k, Nil :: Path vk k k)
vUnitor = Sq (Str (SCons (mapCompanion @hk iObj) SNil) SNil compToId) \\\ iObj @vk @k

-- > K-----K
-- > |     |
-- > |  @  |
-- > |  v  |
-- > K--I--K
vUnitorInv :: forall hk vk k. (HasCompanions hk vk, Ob0 vk k) => Sq '(Nil :: Path hk k k, Nil :: Path vk k k) '(Nil :: Path hk k k, I ::: Nil)
vUnitorInv = Sq (Str SNil (SCons (mapCompanion @hk iObj) SNil) compFromId) \\\ iObj @vk @k

-- > I-f-g-K
-- > | v v |
-- > | \@/ |
-- > |  v  |
-- > I-gof-K
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

-- > I-gof-K
-- > |  v  |
-- > | /@\ |
-- > | v v |
-- > I-f-g-K
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
