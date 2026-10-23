{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Squares, specialized to profunctors: the counterpart of "Proarrow.Equipment.Squares" in
-- @proarrow-equipment@. Data flows rightward along representable wires; effects flow
-- downward along profunctor wires. Paths of profunctors are read right to left, so
-- @[p, q, r]@ is drawn as @r, q, p@ and has composite @r :.: q :.: p@. Paths of
-- 'Representable' profunctors are read top to bottom.
--
-- 'vId' is the identity for '(===)', and 'hId' is the identity for '(|||)'.
--
-- A square's payload is @'Fold' (p '+++' f) :~> 'Fold' (g '+++' q)@, the fold of each side's
-- concatenated path, instead of @'Fold' f ':.:' 'Fold' p :~> 'Fold' q ':.:' 'Fold' g@.
-- "Proarrow.Path" does the associator\/unitor bookkeeping once, and since @'Nil' '+++' ps@ and
-- @ps '+++' 'Nil'@ both reduce to @ps@, combinators with trivial legs need no unitors.
module Proarrow.Squares where

import Data.Kind (Type)
import Prelude (($))

import Proarrow.Adjunction (Proadjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, (//), (:~>), (\\), type (+->))
import Proarrow.Optic (Prostrong (..))
import Proarrow.Path
  ( Fold
  , IsPath
  , IsTight
  , Path (..)
  , SPath (..)
  , Tag (..)
  , appendPath
  , concatFold
  , idN
  , singPath
  , splitFold
  , weakenTight
  , whiskerL
  , whiskerR
  , withAssoc
  , withFoldOb
  , withFoldRep
  , withObAppend
  , type (+++)
  )
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))

infixl 6 |||
infixl 5 ===

-- | The kind of a square @p q f g@.
--
-- > h---p---j
-- > |   |   |
-- > f>--@-->g
-- > |   |   |
-- > i---q---k
type Sq :: Path j h -> Path k i -> Path h i -> Path j k -> Type
data Sq p q f g where
  Sq
    :: (IsPath p, IsPath q, IsTight f, IsTight g)
    => Fold (p +++ f) :~> Fold (g +++ q)
    -> Sq p q f g

-- | Construct a square from its pointwise action. The representable legs act on the
-- input objects through '%'; composition and identity wrappers on those legs are handled
-- automatically. The action must be natural in both objects.
--
-- A traversal crossing, with @[]@ effects and @Maybe@ data:
--
-- >>> import Proarrow.Profunctor.Instance.Star (Star, pattern Star, unStar)
-- >>> import Prelude qualified as P
-- >>> type Crossing = Sq (Star [] ::: Nil) (Star [] ::: Nil) (Star P.Maybe ::: Nil) (Star P.Maybe ::: Nil)
-- >>> let crossing = mkSquare (\(Star f) -> Star (P.traverse f)) :: Crossing
-- >>> unStar (runSquare crossing (Star (\x -> [x, P.not x]))) (P.Just P.True)
-- [Just True,Just False]
-- >>> unStar (runSquare crossing (Star (\x -> [x, P.not x]))) P.Nothing
-- [Nothing]
mkSquare
  :: forall ps qs fs gs
   . (IsPath ps, IsPath qs, IsTight fs, IsTight gs)
  => (forall a b. (Ob a, Ob b) => Fold ps a b -> Fold qs (Fold fs % a) (Fold gs % b))
  -> Sq ps qs fs gs
mkSquare n =
  withFoldOb sps $
    withFoldOb sqs $
      withFoldRep tfs $
        withFoldRep tgs $
          Sq \pf -> case splitFold sps sfs pf of
            f :.: p -> p // concatFold sgs sqs (lmap (index f) (n p) :.: repUniv @(Fold gs))
  where
    sps :: SPath Prof ps
    sps = singPath
    sqs :: SPath Prof qs
    sqs = singPath
    tfs :: SPath Tight fs
    tfs = singPath
    tgs :: SPath Tight gs
    tgs = singPath
    sfs = weakenTight tfs
    sgs = weakenTight tgs

-- | Evaluate a square on a profunctor value. Inverse to 'mkSquare', by naturality and
-- the representability laws. Empty profunctor paths still use the 'Id' wrapper.
runSquare
  :: forall ps qs fs gs a b
   . Sq ps qs fs gs
  -> Fold ps a b
  -> Fold qs (Fold fs % a) (Fold gs % b)
runSquare (Sq n) p =
  withFoldOb sps $
    withFoldOb sqs $
      withFoldRep tfs $
        withFoldRep tgs $
          p // case splitFold sgs sqs (n (concatFold sps sfs (repUniv @(Fold fs) :.: p))) of
            q :.: g -> rmap (index g) q
  where
    sps :: SPath Prof ps
    sps = singPath
    sqs :: SPath Prof qs
    sqs = singPath
    tfs :: SPath Tight fs
    tfs = singPath
    tgs :: SPath Tight gs
    tgs = singPath
    sfs = weakenTight tfs
    sgs = weakenTight tgs

-- | The empty square for an object.
--
-- > K-------K
-- > |       |
-- > |       |
-- > |       |
-- > K-------K
object :: (CategoryOf k) => Sq (Nil :: Path k k) Nil Nil Nil
object = Sq idN

-- | A square between profunctors, with trivial representable legs.
--
-- > K---p---J
-- > |   |   |
-- > |   @   |
-- > |   |   |
-- > K---q---J
vArr :: (Profunctor p, Profunctor q) => p :~> q -> Sq (p ::: Nil) (q ::: Nil) Nil Nil
vArr = Sq

-- | A vertical identity square.
--
-- > J---p---K
-- > |   |   |
-- > |   |   |
-- > |   |   |
-- > J---p---K
vId :: (Profunctor p) => Sq (p ::: Nil) (p ::: Nil) Nil Nil
vId = vArr idN

-- | A square between representable profunctors, with trivial profunctor legs.
--
-- > J-------J
-- > |       |
-- > f>--@-->g
-- > |       |
-- > K-------K
hArr :: (Representable f, Representable g) => f :~> g -> Sq Nil Nil (f ::: Nil) (g ::: Nil)
hArr = Sq

-- | A horizontal identity square.
--
-- > J-------J
-- > |       |
-- > f>----->f
-- > |       |
-- > K-------K
hId :: (Representable f) => Sq Nil Nil (f ::: Nil) (f ::: Nil)
hId = hArr idN

-- | Horizontal composition, with the left square first. Profunctor paths concatenate
-- from right to left, matching the order of profunctor composition.
--
-- > H--p--L--r--M       H--r+p--M
-- > |     |     |       |       |
-- > f--@--g--@--e   =   f---@---e
-- > |     |     |       |       |
-- > I--q--J--s--K       I--s+q--K
(|||) :: forall ps qs fs gs rs ss es. Sq ps qs fs gs -> Sq rs ss gs es -> Sq (rs +++ ps) (ss +++ qs) fs es
Sq l ||| Sq r =
  withObAppend @Prof @rs @ps srs $
    withObAppend @Prof @ss @qs sss $
      withAssoc @es @ss @qs @Tight $
        withAssoc @rs @ps @fs @Prof $
          withAssoc @rs @gs @qs @Prof $
            Sq $
              whiskerR (appendPath srs sgs) (appendPath ses sss) sqs r
                . whiskerL srs (appendPath sps sfs) (appendPath sgs sqs) l
  where
    srs :: SPath Prof rs
    srs = singPath
    sss :: SPath Prof ss
    sss = singPath
    sps :: SPath Prof ps
    sps = singPath
    sqs :: SPath Prof qs
    sqs = singPath
    sfs :: SPath Prof fs
    sfs = weakenTight singPath
    sgs :: SPath Prof gs
    sgs = weakenTight singPath
    ses :: SPath Prof es
    ses = weakenTight singPath

-- | Vertical composition, with the top square first.
--
-- > L---p---M       L---p---M
-- > |       |       |       |
-- > d---@---e       |       |
-- > |       |       |       |
-- > H---q---J   =  d+f--@--e+g
-- > |       |       |       |
-- > f---@---g       |       |
-- > |       |       |       |
-- > I---r---K       I---r---K
(===) :: forall ps qs rs ds es fs gs. Sq ps qs ds es -> Sq qs rs fs gs -> Sq ps rs (ds +++ fs) (es +++ gs)
Sq top === Sq bot =
  withObAppend @Tight @ds @fs tds $
    withObAppend @Tight @es @gs tes $
      withAssoc @ps @ds @fs @Prof $
        withAssoc @es @qs @fs @Tight $
          withAssoc @es @gs @rs @Tight $
            Sq $
              whiskerL ses (appendPath sqs sfs) (appendPath sgs srs) bot
                . whiskerR (appendPath sps sds) (appendPath ses sqs) sfs top
  where
    tds :: SPath Tight ds
    tds = singPath
    tes :: SPath Tight es
    tes = singPath
    sps :: SPath Prof ps
    sps = singPath
    sqs :: SPath Prof qs
    sqs = singPath
    srs :: SPath Prof rs
    srs = singPath
    sds :: SPath Prof ds
    sds = weakenTight tds
    ses :: SPath Prof es
    ses = weakenTight tes
    sfs :: SPath Prof fs
    sfs = weakenTight singPath
    sgs :: SPath Prof gs
    sgs = weakenTight singPath

-- | Bend a representable profunctor from the left edge to its companion on the bottom edge.
--
-- > J-------J
-- > |       |
-- > f>--\   |
-- > |   v   |
-- > K---f---J
toBottom :: (Representable f) => Sq Nil (f ::: Nil) (f ::: Nil) Nil
toBottom = Sq idN

-- | Bend a representable profunctor from the left edge to its conjoint on the top edge.
--
-- > J---f---K
-- > |   ^   |
-- > f>--/   |
-- > |       |
-- > K-------K
toTop :: forall f f'. (Proadjunction f f', Representable f) => Sq (f' ::: Nil) Nil (f ::: Nil) Nil
toTop = Sq (counitNat @f @f')

-- | Bend a companion from the top edge back to a representable profunctor on the right edge.
--
-- > K---f---J
-- > |   v   |
-- > |   \-->f
-- > |       |
-- > K-------K
fromTop :: (Representable f) => Sq (f ::: Nil) Nil Nil (f ::: Nil)
fromTop = Sq idN

-- | Bend a conjoint from the bottom edge back to a representable profunctor on the right edge.
--
-- > J-------J
-- > |       |
-- > |   /-->f
-- > |   ^   |
-- > J---f---K
fromBottom :: forall f f'. (Proadjunction f f', Representable f) => Sq Nil (f' ::: Nil) Nil (f ::: Nil)
fromBottom = Sq (unitNat @f @f')

unitNat :: forall p q. (Proadjunction p q) => Id :~> q :.: p
unitNat (Id f) = rmap f (Adj.unit @p @q) \\ f

counitNat :: forall p q. (Proadjunction p q) => p :.: q :~> Id
counitNat pq = Id (Adj.counit pq)

-- > K-------K
-- > |       |
-- > I>--@   |
-- > |       |
-- > K-------K
hUnitor :: forall k. (CategoryOf k) => Sq Nil Nil ((Id :: CAT k) ::: Nil) Nil
hUnitor = hSplitAll @Nil

-- > K-------K
-- > |       |
-- > |   @-->I
-- > |       |
-- > K-------K
hUnitorInv :: forall k. (CategoryOf k) => Sq Nil Nil Nil ((Id :: CAT k) ::: Nil)
hUnitorInv = hCombineAll @Nil

-- > I---------I
-- > f>---\    |
-- > |    @->gof
-- > g>---/    |
-- > K---------K
hCombine :: forall f g. (Representable f, Representable g) => Sq Nil Nil (f ::: g ::: Nil) (g :.: f ::: Nil)
hCombine = hCombineAll @(f ::: g ::: Nil)

-- > I---------I
-- > |    /--->f
-- > gof>-@    |
-- > |    \--->g
-- > K---------K
hSplit :: forall f g. (Representable f, Representable g) => Sq Nil Nil (g :.: f ::: Nil) (f ::: g ::: Nil)
hSplit = hSplitAll @(f ::: g ::: Nil)

-- | Combine a path of representable profunctors into one composed representable profunctor.
--
-- > J---------J
-- > f>---\    |
-- > |    @--->F
-- > g>---/    |
-- > K---------K
hCombineAll :: forall fs. (IsTight fs) => Sq Nil Nil fs (Fold fs ::: Nil)
hCombineAll = withFoldRep tfs (Sq idN)
  where
    tfs :: SPath Tight fs
    tfs = singPath

-- | Split one composed representable profunctor into a path of representable profunctors.
--
-- > J---------J
-- > |    /--->f
-- > F>---@    |
-- > |    \--->g
-- > K---------K
hSplitAll :: forall fs. (IsTight fs) => Sq Nil Nil (Fold fs ::: Nil) fs
hSplitAll = withFoldRep tfs (Sq idN)
  where
    tfs :: SPath Tight fs
    tfs = singPath

-- > K---I---K
-- > |   |   |
-- > |   @   |
-- > |       |
-- > K-------K
vUnitor :: forall k. (CategoryOf k) => Sq ((Id :: CAT k) ::: Nil) Nil Nil Nil
vUnitor = vSplitAll @Nil

-- > K-------K
-- > |       |
-- > |   @   |
-- > |   |   |
-- > K---I---K
vUnitorInv :: forall k. (CategoryOf k) => Sq Nil ((Id :: CAT k) ::: Nil) Nil Nil
vUnitorInv = vCombineAll @Nil

-- > K-q---p-J
-- > |  \ /  |
-- > |   @   |
-- > |   |   |
-- > K--qop--J
vCombine :: forall p q. (Profunctor p, Profunctor q) => Sq (p ::: q ::: Nil) (q :.: p ::: Nil) Nil Nil
vCombine = vCombineAll @(p ::: q ::: Nil)

-- > K--qop--J
-- > |   |   |
-- > |   @   |
-- > |  / \  |
-- > K-q---p-J
vSplit :: forall p q. (Profunctor p, Profunctor q) => Sq (q :.: p ::: Nil) (p ::: q ::: Nil) Nil Nil
vSplit = vSplitAll @(p ::: q ::: Nil)

-- | Combine a path of profunctors into one composed profunctor.
--
-- > K-q---p-J
-- > |  \ /  |
-- > |   @   |
-- > |   |   |
-- > K---F---J
vCombineAll :: forall ps. (IsPath ps) => Sq ps (Fold ps ::: Nil) Nil Nil
vCombineAll = withFoldOb sp (Sq idN)
  where
    sp :: SPath Prof ps
    sp = singPath

-- | Split one composed profunctor into a path of profunctors.
--
-- > K---F---J
-- > |   |   |
-- > |   @   |
-- > |  / \  |
-- > K-q---p-J
vSplitAll :: forall ps. (IsPath ps) => Sq (Fold ps ::: Nil) ps Nil Nil
vSplitAll = withFoldOb sp (Sq idN)
  where
    sp :: SPath Prof ps
    sp = singPath

-- | The unit of an adjunction.
--
-- > J-------J
-- > |       |
-- > | /-@-\ |
-- > | |   | |
-- > J-q---p-J
unit :: forall p q. (Proadjunction p q) => Sq Nil (p ::: q ::: Nil) Nil Nil
unit =
  vCombineAll @Nil
    === vArr (unitNat @p @q)
    === vSplitAll @(p ::: q ::: Nil)

-- | The counit of an adjunction.
--
-- > K-p---q-K
-- > | |   | |
-- > | \-@-/ |
-- > |       |
-- > K-------K
counit :: forall p q. (Proadjunction p q) => Sq (q ::: p ::: Nil) Nil Nil Nil
counit =
  vCombineAll @(q ::: p ::: Nil)
    === vArr (counitNat @p @q)
    === vSplitAll @Nil

-- | A square introducing an effect @r@ between representable data shapes @f@ and @g@,
-- with no incoming effect. Optics consume and produce squares of this same shape.
--
-- > X-----------X
-- > |           |
-- > f>----@---->g
-- > |     |     |
-- > J-----r-----K
type InputSquare :: (k +-> j) -> (x +-> j) -> (x +-> k) -> Type
type InputSquare r f g = Sq Nil (r ::: Nil) (f ::: Nil) (g ::: Nil)

-- | Absorb a general witness pair around an effect with 'proact'. All three incoming
-- profunctors are vertical or diagonal wires. No representability is required of @p@ or @q@.
--
-- > J--p--r--q--K
-- > |   \ | /   |
-- > |    @@@    |
-- > |     |     |
-- > J-----r-----K
proSquare
  :: forall {j} {k} w (r :: k +-> j) (p :: j +-> j) (q :: k +-> k)
   . (Prostrong w r, w p q, Profunctor p, Profunctor q)
  => Sq (q ::: r ::: p ::: Nil) (r ::: Nil) Nil Nil
proSquare =
  vCombineAll @(q ::: r ::: p ::: Nil)
    === vArr (proact @w @r @p @q)

-- | An optic between representable data shapes, programmed by composing squares.
-- Its legs @s :~> p :.: a@ and @b :~> q :.: t@ introduce the residual profunctors
-- @p@ and @q@, which are absorbed with the input effect by 'proSquare'. All four
-- data shapes share an index category. Constant shapes from the terminal category
-- recover optics between individual objects.
--
-- Wire names appear on borders; each contiguous run of @\@@ marks one transformation. The top central
-- square is the input, the left square unpacks, and the right square rebuilds. The
-- lower square absorbs their three outgoing effects. Residual profunctors stay
-- vertical or diagonal; only representable data wires run horizontally:
--
-- > X-----+-----+-----X
-- > |     |     |     |
-- > s>-@->a>-@->b>-@->t
-- > |  |  |  |  |  |  |
-- > +--p--+--r--+--q--+
-- > |   \    |    /   |
-- > |    @@@@@@@@@    |
-- > |        |        |
-- > J--------r--------K
--
-- The outer boundary is another input-shaped square, now with data legs @s@ and @t@,
-- so it can be used as the input to another optic.
opticSquare
  :: forall {j} {k} {x} w (r :: k +-> j) (p :: j +-> j) (q :: k +-> k) (s :: x +-> j) (t :: x +-> k) (a :: x +-> j) (b :: x +-> k)
   . (Prostrong w r, w p q, Profunctor p, Profunctor q)
  => InputSquare p s a -> InputSquare q b t -> InputSquare r a b -> InputSquare r s t
opticSquare unpack rebuild input =
  unpack ||| input ||| rebuild
    === proSquare @w
