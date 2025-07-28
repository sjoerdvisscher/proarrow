{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares where

import Data.Functor.Const (Const (..))
import Data.Kind (Type)
import Proarrow.Category.Bicategory (Bicategory (..), Ob')
import Proarrow.Category.Bicategory.Prof (FUN, PROFK (..), Prof (..))
import Proarrow.Category.Bicategory.Strictified
  ( Fold
  , IsPath (..)
  , Path (..)
  , SPath (..)
  , Strictified (..)
  , asObj
  , companionFold
  , fold
  , foldCompanion
  , mapCompanionSPath
  , singleton
  , type (+++)
  )
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..))
import Proarrow.Category.Equipment qualified as E
import Proarrow.Core (CategoryOf (..), Obj, Promonad ((.)), id, obj, (:~>), (\\))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (RepCostar (..), Representable)
import Proarrow.Profunctor.Star (Star (..))
import Prelude (Either, either)

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
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
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
  => Obj f
  -> Sq '(Nil :: Path hk j j, f ::: Nil) '(Nil :: Path hk k k, f ::: Nil)
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

-- > K--I--K
-- > |  v  |
-- > |  @  |
-- > |     |
-- > K-----K
vUnitor
  :: forall hk vk k
   . (HasCompanions hk vk, Ob0 vk k)
  => Sq '(Nil :: Path hk k k, I ::: Nil) '(Nil :: Path hk k k, Nil :: Path vk k k)
vUnitor = vSplitAll

-- > K-----K
-- > |     |
-- > |  @  |
-- > |  v  |
-- > K--I--K
vUnitorInv
  :: forall hk vk k
   . (HasCompanions hk vk, Ob0 vk k)
  => Sq '(Nil :: Path hk k k, Nil :: Path vk k k) '(Nil :: Path hk k k, I ::: Nil)
vUnitorInv = vCombineAll

-- > I-f-g-K
-- > | v v |
-- > | \@/ |
-- > |  v  |
-- > I-gof-K
vCombine
  :: forall {hk} {vk} {i} {j} {k} (f :: vk i j) (g :: vk j k)
   . (HasCompanions hk vk, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob f, Ob g)
  => Sq '(Nil :: Path hk i i, f ::: g ::: Nil) '(Nil, g `O` f ::: Nil)
vCombine = vCombineAll

-- > I-gof-K
-- > |  v  |
-- > | /@\ |
-- > | v v |
-- > I-f-g-K
vSplit
  :: forall {hk} {vk} {i} {j} {k} (f :: vk i j) (g :: vk j k)
   . (HasCompanions hk vk, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob f, Ob g)
  => Sq '(Nil :: Path hk i i, g `O` f ::: Nil) '(Nil, f ::: g ::: Nil)
vSplit = vSplitAll

-- | Combine a whole bunch of vertical arrows into one composed arrow.
--
-- > J-p..-K
-- > | vvv |
-- > | \@/ |
-- > |  v  |
-- > J--f--K
vCombineAll
  :: forall {hk} {vk} {j} {k} (ps :: Path vk j k)
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob ps)
  => Sq '(Nil :: Path hk j j, ps) '(Nil :: Path hk k k, Fold ps ::: Nil)
vCombineAll =
  let ps = singPath @ps; fps = fold ps
  in Sq (Str (mapCompanionSPath ps) (SCons (mapCompanion fps) SNil) (foldCompanion ps)) \\ fps

-- | Split one composed arrow into a whole bunch of vertical arrows.
--
-- > J--f--K
-- > |  v  |
-- > | /@\ |
-- > | vvv |
-- > J-p..-K
vSplitAll
  :: forall {hk} {vk} {j} {k} (ps :: Path vk j k)
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob ps)
  => Sq '(Nil :: Path hk j j, Fold ps ::: Nil) '(Nil :: Path hk k k, ps)
vSplitAll =
  let ps = singPath @ps; fps = fold ps; cps = mapCompanionSPath @hk ps
  in Sq (Str (SCons (mapCompanion fps) SNil) cps (companionFold ps)) \\ fps \\ asObj cps

-- | Combine a whole bunch of horizontal proarrows into one composed proarrow.
--
-- > K-----K
-- > p--\  |
-- > :--@--f
-- > :--/  |
-- > J-----J
hCombineAll
  :: forall {hk} {vk} {j} {k} (ps :: Path hk j k)
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob ps)
  => Sq '(ps, Nil :: Path vk k k) '(Fold ps ::: Nil, Nil)
hCombineAll = let ps = singPath @ps; fps = fold ps in Sq (Str ps (SCons fps SNil) fps) \\\ fps

-- | Split one composed proarrow into a whole bunch of horizontal proarrows.
--
-- > K-----K
-- > |  /--p
-- > f--@--:
-- > |  \--:
-- > J-----J
hSplitAll
  :: forall {hk} {vk} {j} {k} (ps :: Path hk j k)
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob ps)
  => Sq '(Fold ps ::: Nil, Nil :: Path vk k k) '(ps, Nil)
hSplitAll = let ps = singPath @ps; fps = fold ps in Sq (Str (SCons fps SNil) ps fps) \\\ fps

-- | Optics in proarrow equipments.
--
-- > J-------J
-- > s>-\ /->a
-- > |   @   |
-- > t<-/ \-<b
-- > K-------K
type Optic hk (s :: vk x j) (t :: vk x k) (a :: vk z j) (b :: vk z k) =
  Sq '(Conjoint hk t ::: Companion hk s ::: Nil, Nil :: Path vk j j) '(Conjoint hk b ::: Companion hk a ::: Nil, Nil)

type ProfOptic s t a b = Optic PROFK (FUN s) (FUN t) (FUN a) (FUN b)
mkProfOptic
  :: (Representable s, Representable t, Representable a, Representable b)
  => s :.: RepCostar t :~> a :.: RepCostar b -> ProfOptic s t a b
mkProfOptic n = Sq (Str (SCons obj (SCons obj SNil)) (SCons obj (SCons obj SNil)) (Prof n))

type HaskOptic s t a b = ProfOptic (Star (Const s :: Type -> Type)) (Star (Const t)) (Star a) (Star b)

type Lens s t a b = HaskOptic s t ((,) a) ((,) b)
mkLens :: (s -> (a, b -> t)) -> Lens s t a b
mkLens f = mkProfOptic \(Star s :.: RepCostar t) -> Star (f . getConst . s) :.: RepCostar (\(b, bt) -> t (Const (bt b)))

type Prism s t a b = HaskOptic s t (Either a) (Either b)
mkPrism :: (b -> t) -> (s -> Either a t) -> Prism s t a b
mkPrism to from = mkProfOptic \(Star s :.: RepCostar t) -> Star (from . getConst . s) :.: RepCostar (t . Const . either to id)
