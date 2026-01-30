{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares where

import Data.Functor.Compose (Compose (..))
import Prelude (Either (..), Traversable, either, ($))

import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..), obj1, (||))
import Proarrow.Category.Bicategory.Prof (PROFK (..), Prof (..))
import Proarrow.Category.Bicategory.Strictified
  ( Fold
  , Path (..)
  , Strictified (..)
  , combineAll
  , splitAll
  , withIsObTagFold
  , type (+++)
  )
import Proarrow.Category.Bicategory.Sub (SUBCAT (..), Sub (Sub))
import Proarrow.Category.Equipment (Equipment, IsCotight, IsTight, Tight, TightPair)
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), (:~>), (\\), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Star (Star, pattern Star)

-- | The kind of a square @'(q, f) '(p, g)@.
--
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--g--k
type SQ' (kk :: CAT c) h i j k = (kk k i, SUBCAT Tight kk j k) +-> (kk j h, SUBCAT Tight kk h i)

type SQ (kk :: CAT c) = forall {h} {i} {j} {k}. SQ' kk h i j k

type Sq' :: forall {c} {kk :: CAT c}. SQ kk
data Sq' pf qg where
  Sq
    :: forall {kk} {h} {i} {j} {k} (p :: Path kk j h) (q :: Path kk k i) (f :: Path kk h i) (g :: Path kk j k)
     . (Ob p, Ob q, IsTight f, IsTight g)
    => f `O` p ~> q `O` g
    -> Sq' '(p, SUB f) '(q, SUB g)

type Sq p q f g = Sq' '(p, SUB f) '(q, SUB g)

instance (Bicategory kk, Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k) => Profunctor (Sq' :: SQ' kk h i j k) where
  dimap (p :**: Sub f) (q :**: Sub g) (Sq sq) = Sq ((q `o` g) . sq . (f `o` p)) \\ p \\ f \\ q \\ g
  r \\ Sq sq = r \\ sq

infixl 6 |||
infixl 5 ===

-- | The empty square for an object.
--
-- > K-----K
-- > |     |
-- > |     |
-- > |     |
-- > K-----K
object :: (Equipment kk, Ob0 kk k) => Sq (Nil :: Path kk k k) (Nil :: Path kk k k) Nil Nil
object = Sq id

-- | Make a square from a horizontal proarrow
--
-- > K-----K
-- > |     |
-- > p--@--q
-- > |     |
-- > J-----J
hArr
  :: forall {kk} {j} {k} (p :: kk j k) q
   . (Equipment kk)
  => p ~> q
  -> Sq (p ::: Nil) (q ::: Nil) Nil Nil
hArr pq = Sq (St pq) \\\ pq

-- | A horizontal identity square.
--
-- > J-----J
-- > |     |
-- > p-----p
-- > |     |
-- > K-----K
hId
  :: forall {kk} {j} {k} (p :: kk j k)
   . (Equipment kk, Ob0 kk j, Ob0 kk k, Ob p)
  => Sq (p ::: Nil) (p ::: Nil) Nil Nil
hId = hArr id

-- | Make a square from a vertical arrow
--
-- > J--f--K
-- > |  v  |
-- > |  @  |
-- > |  v  |
-- > J--g--K
vArr
  :: forall {kk} {j} {k} (f :: kk j k) g
   . (Equipment kk, IsTight f, IsTight g)
  => f ~> g
  -> Sq Nil Nil (f ::: Nil) (g ::: Nil)
vArr fg = Sq (St fg) \\\ fg

-- | A vertical identity square.
--
-- > J--f--K
-- > |  v  |
-- > |  |  |
-- > |  v  |
-- > J--f--K
vId
  :: forall {kk} {j} {k} (f :: kk j k)
   . (Equipment kk, IsTight f)
  => Sq Nil Nil (f ::: Nil) (f ::: Nil)
vId = withOb0s @kk @f (Sq id)

-- | Horizontal composition
--
-- > L--d--H     H--f--I     L-d+f-I
-- > |  v  |     |  v  |     |  v  |
-- > p--@--q ||| q--@--r  =  p--@--r
-- > |  v  |     |  v  |     |  v  |
-- > M--e--J     J--g--K     M-e+g-K
(|||)
  :: forall {kk} {h} {l} {m} (ps :: Path kk m l) qs rs (ds :: Path kk l h) es fs gs
   . (Equipment kk)
  => Sq ps qs ds es
  -> Sq qs rs fs gs
  -> Sq ps rs (ds +++ fs) (es +++ gs)
Sq l ||| Sq r =
  withOb2 @(SUBCAT Tight (Path kk)) @(SUB fs) @(SUB ds) $
    withOb2 @(SUBCAT Tight (Path kk)) @(SUB gs) @(SUB es) $
      Sq
        (associator @_ @rs @gs @es . (r || obj1 @es) . associator @_ @fs @qs @es . (obj1 @fs || l) . associator @_ @fs @ds @ps)

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
  :: forall {kk} {h} {i} {j} {l} (ps :: Path kk l j) qs rs ss (es :: Path kk h i) fs gs
   . (Equipment kk)
  => Sq rs ss es fs
  -> Sq ps qs fs gs
  -> Sq (ps +++ rs) (qs +++ ss) es gs
Sq l === Sq r =
  withOb2 @_ @rs @ps $
    withOb2 @_ @ss @qs $
      Sq
        (associatorInv @_ @ss @qs @gs . (obj1 @ss || r) . associator @_ @ss @fs @ps . (l || obj1 @ps) . associator @_ @es @rs @ps)

-- | Bend a vertical arrow in the companion direction.
--
-- > J--f--K
-- > |  v  |
-- > |  \->f
-- > |     |
-- > J-----J
toRight
  :: forall {kk} {j} {k} (f :: kk j k)
   . (Equipment kk, IsTight f)
  => Sq Nil (f ::: Nil) (f ::: Nil) Nil
toRight = withOb0s @kk @f $ Sq id

-- | Bend a vertical arrow in the conjoint direction.
--
-- > J--f--K
-- > |  v  |
-- > f<-/  |
-- > |     |
-- > K-----K
toLeft
  :: forall {kk} {j} {k} (f :: kk j k) f'
   . (Equipment kk, TightPair f f')
  => Sq (f' ::: Nil) Nil (f ::: Nil) Nil
toLeft = withOb0s @kk @f $ Sq (St (counit @f @f'))

-- | Bend a companion proarrow back to a vertical arrow.
--
-- > K-----K
-- > |     |
-- > f>-\  |
-- > |  v  |
-- > J--f--K
fromLeft
  :: forall {kk} {j} {k} (f :: kk j k)
   . (Equipment kk, IsTight f)
  => Sq (f ::: Nil) Nil Nil (f ::: Nil)
fromLeft = withOb0s @kk @f $ Sq id

-- | Bend a conjoint proarrow back to a vertical arrow.
--
-- > J-----J
-- > |     |
-- > |  /-<f
-- > |  v  |
-- > J--f--K
fromRight
  :: forall {kk} {j} {k} (f :: kk j k) f'
   . (Equipment kk, TightPair f f')
  => Sq Nil (f' ::: Nil) Nil (f ::: Nil)
fromRight = withOb0s @kk @f $ Sq (St (unit @f @f'))

-- > K--I--K
-- > |  v  |
-- > |  @  |
-- > |     |
-- > K-----K
vUnitor
  :: forall kk k
   . (Equipment kk, Ob0 kk k)
  => Sq Nil Nil ((I :: kk k k) ::: Nil) Nil
vUnitor = vSplitAll

-- > K-----K
-- > |     |
-- > |  @  |
-- > |  v  |
-- > K--I--K
vUnitorInv
  :: forall kk k
   . (Equipment kk, Ob0 kk k)
  => Sq Nil Nil Nil ((I :: kk k k) ::: Nil)
vUnitorInv = vCombineAll

-- > I-f-g-K
-- > | v v |
-- > | \@/ |
-- > |  v  |
-- > I-gof-K
vCombine
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k)
   . (Equipment kk, IsTight p, IsTight q)
  => Sq Nil Nil (p ::: q ::: Nil) (q `O` p ::: Nil)
vCombine = withOb0s @kk @p $ withOb0s @kk @q vCombineAll

-- > I-gof-K
-- > |  v  |
-- > | /@\ |
-- > | v v |
-- > I-f-g-K
vSplit
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k)
   . (Equipment kk, IsTight p, IsTight q)
  => Sq Nil Nil (q `O` p ::: Nil) (p ::: q ::: Nil)
vSplit = withOb0s @kk @p $ withOb0s @kk @q vSplitAll

-- | Combine a whole bunch of vertical arrows into one composed arrow.

-- > J-p..-K
-- > | vvv |
-- > | \@/ |
-- > |  v  |
-- > J--f--K
vCombineAll
  :: forall {kk} {j} {k} (ps :: Path kk j k)
   . (Equipment kk, IsTight ps)
  => Sq Nil Nil ps (Fold ps ::: Nil)
vCombineAll = let n = combineAll @ps in withIsObTagFold @Tight @ps (Sq n \\ n)

-- | Split one composed arrow into a whole bunch of vertical arrows.
--
-- > J--f--K
-- > |  v  |
-- > | /@\ |
-- > | vvv |
-- > J-p..-K
vSplitAll
  :: forall {kk} {j} {k} (ps :: Path kk j k)
   . (Equipment kk, IsTight ps)
  => Sq Nil Nil (Fold ps ::: Nil) ps
vSplitAll = let n = splitAll @ps in withIsObTagFold @Tight @ps (Sq n \\ n)

-- | Combine a whole bunch of horizontal proarrows into one composed proarrow.
--
-- > K-----K
-- > p--\  |
-- > :--@--F
-- > :--/  |
-- > J-----J
hCombineAll
  :: forall {kk} {j} {k} (ps :: Path kk j k)
   . (Equipment kk, Ob0 kk j, Ob0 kk k, Ob ps)
  => Sq ps (Fold ps ::: Nil) Nil Nil
hCombineAll = let n = combineAll @ps in Sq n \\ n

-- | Split one composed proarrow into a whole bunch of horizontal proarrows.
--
-- > K-----K
-- > |  /--p
-- > F--@--:
-- > |  \--:
-- > J-----J
hSplitAll
  :: forall {kk} {j} {k} (ps :: Path kk j k)
   . (Equipment kk, Ob0 kk j, Ob0 kk k, Ob ps)
  => Sq (Fold ps ::: Nil) ps Nil Nil
hSplitAll = let n = splitAll @ps in Sq n \\ n

-- | Optics in proarrow equipments.
--
-- > J-------J
-- > s>--@-->a
-- > |   @   |
-- > t<--@--<b
-- > K-------K
type Optic (a :: kk z j) (b :: kk k z) (s :: kk x j) (t :: kk k x) =
  (IsTight a, IsCotight b, IsTight s, IsCotight t) => Sq (t ::: s ::: Nil) (b ::: a ::: Nil) Nil Nil

-- > J-------J
-- > s>-\ /->a
-- > |   @   |
-- > |   v   |
-- > X---m---Z

-- > X---m---Z
-- > |   v   |
-- > |   @   |
-- > t<-/ \-<b
-- > K-------K

-- > J-------J     J-------J
-- > a>--@   |     s>--@   |
-- > |   @---p ==> |   @---p
-- > b<--@   |     t<--@   |
-- > K-------K     K-------K

-- > J-------J     J-------J
-- > a>----->a     s>--@-->a
-- > |       | ==> |   @   |
-- > b<-----<b     t<--@--<b
-- > K-------K     K-------K

-- > J-------J     J-------J
-- > |   @-->a     |   @-->a
-- > |   @   |     |   @-->m
-- > p---@   | ==> p---@   |
-- > |   @   |     |   @--<m
-- > |   @--<b     |   @--<b
-- > K-------K     K-------K

type ProfOptic a b s t = Optic (PK a) (PK b) (PK s) (PK t)
mkProfOptic :: s :.: t :~> a :.: b -> ProfOptic a b s t
mkProfOptic n = Sq (St (Prof n))

type HaskOptic a b s t = ProfOptic (Star a) (Costar b) (Star s) (Costar t)
mkHaskOptic
  :: (Functor a, Functor b, Functor s, Functor t)
  => (forall x r. (Ob x) => (forall y. (Ob y) => (s x ~> a y) -> (b y ~> t x) -> r) -> r) -> HaskOptic a b s t
mkHaskOptic k = mkProfOptic \(Star @y s :.: Costar t) -> k @y \get put -> Star (get . s) :.: Costar (t . put)

type Lens s t a b = HaskOptic ((,) a) ((,) b) ((,) s) ((,) t)
mkLens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
mkLens f g = mkHaskOptic (\k -> k (\(s, x) -> (f s, (g s, x))) (\(b, (bt, x)) -> (bt b, x)))

type Prism s t a b = HaskOptic (Either a) (Either b) (Either s) (Either t)
mkPrism :: (s -> Either a t) -> (b -> t) -> Prism s t a b
mkPrism f g = mkHaskOptic (\k -> k (either (either Left (Right . Left) . f) (Right . Right)) (either (Left . g) id))

data FlipApp a f = FlipApp {unFlipApp :: f a}
instance (Ob a) => Functor (FlipApp a) where
  map (Nat f) (FlipApp x) = FlipApp (f x)
type Traversal s t a b = HaskOptic (FlipApp a) (FlipApp b) (FlipApp s) (FlipApp t)
mkTraversal :: (Traversable f, Functor f) => Traversal (f a) (f b) a b
mkTraversal = mkHaskOptic (\k -> k (FlipApp . Compose . unFlipApp) (FlipApp . getCompose . unFlipApp))
