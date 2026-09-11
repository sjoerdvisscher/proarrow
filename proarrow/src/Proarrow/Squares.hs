{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Squares, specialized to profunctors.
--
-- This is the profunctor-specific counterpart of "Proarrow.Equipment.Squares" in
-- @proarrow-equipment@: instead of squares over an arbitrary proarrow equipment, the
-- legs here are 'Proarrow.Path.Path's of plain profunctors (horizontal) or
-- 'Representable' profunctors (vertical, playing the role of the tight morphisms of the
-- @Prof@ equipment). "Proarrow.Path" does the associator\/unitor bookkeeping once, by
-- induction over the path, so the combinators below never have to. A square's payload is
-- stated as @'Fold' (p '+++' f) :~> 'Fold' (g '+++' q)@ (the fold of each side's
-- concatenated path) rather than @'Fold' f ':.:' 'Fold' p :~> 'Fold' q ':.:' 'Fold' g@: it
-- means combinators whose legs are trivial (@'Nil'@ or a single element) need no unitors
-- at all, since e.g. @'Nil' '+++' ps@ and @ps '+++' 'Nil'@ both reduce to @ps@ for free.
module Proarrow.Squares where

import Data.Kind (Type)
import Prelude (($))

import Proarrow.Adjunction (Proadjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Category.Instance.Prof qualified as P
import Proarrow.Category.Monoidal (Monoidal (..), type (**))
import Proarrow.Category.Monoidal.Action (Act, ActionAt, MonoidalAction (..), actHom)
import Proarrow.Category.Monoidal.Endo (ENDO (..), Precomp)
import Proarrow.Category.Monoidal.Rev (REV (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), obj, rmap, (//), (:~>), (\\), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Optic (ExOptic (..))
import Proarrow.Optic.Action (ActFl (..))
import Proarrow.Path
  ( Fold
  , IsPath
  , IsTight
  , Path (..)
  , SPath (..)
  , Tag (..)
  , appendPath
  , idN
  , singPath
  , weakenTight
  , whiskerL
  , whiskerR
  , withAssoc
  , withFoldOb
  , withFoldRep
  , withObAppend
  , type (+++)
  )
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), Representable (..))

infixl 6 |||
infixl 5 ===

-- | The kind of a square @p q f g@.
--
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--g--k
type Sq :: Path j h -> Path k i -> Path h i -> Path j k -> Type
data Sq p q f g where
  Sq
    :: (IsPath p, IsPath q, IsTight f, IsTight g)
    => Fold (p +++ f) :~> Fold (g +++ q)
    -> Sq p q f g

-- | The empty square for an object.
--
-- > K-----K
-- > |     |
-- > |     |
-- > |     |
-- > K-----K
object :: (CategoryOf k) => Sq (Nil :: Path k k) Nil Nil Nil
object = Sq idN

-- | Make a square from a horizontal proarrow.
--
-- > K-----K
-- > |     |
-- > p--@--q
-- > |     |
-- > J-----J
hArr :: (Profunctor p, Profunctor q) => p :~> q -> Sq (p ::: Nil) (q ::: Nil) Nil Nil
hArr = Sq

-- | A horizontal identity square.
--
-- > J-----J
-- > |     |
-- > p-----p
-- > |     |
-- > K-----K
hId :: (Profunctor p) => Sq (p ::: Nil) (p ::: Nil) Nil Nil
hId = hArr idN

-- | Make a square from a vertical arrow.
--
-- > J--f--K
-- > |  v  |
-- > |  @  |
-- > |  v  |
-- > J--g--K
vArr :: (Representable f, Representable g) => f :~> g -> Sq Nil Nil (f ::: Nil) (g ::: Nil)
vArr = Sq

-- | A vertical identity square.
--
-- > J--f--K
-- > |  v  |
-- > |  |  |
-- > |  v  |
-- > J--f--K
vId :: (Representable f) => Sq Nil Nil (f ::: Nil) (f ::: Nil)
vId = vArr idN

-- | Horizontal composition.
--
-- > L--d--H     H--f--I     L-d+f-I
-- > |  v  |     |  v  |     |  v  |
-- > p--@--q ||| q--@--r  =  p--@--r
-- > |  v  |     |  v  |     |  v  |
-- > M--e--J     J--g--K     M-e+g-K
(|||) :: forall ps qs rs ds es fs gs. Sq ps qs ds es -> Sq qs rs fs gs -> Sq ps rs (ds +++ fs) (es +++ gs)
Sq l ||| Sq r =
  withObAppend @Tight @ds @fs tds $
    withObAppend @Tight @es @gs tes $
      withAssoc @ps @ds @fs @Prof $
        withAssoc @es @qs @fs @Tight $
          withAssoc @es @gs @rs @Tight $
            Sq $
              whiskerL ses (appendPath sqs sfs) (appendPath sgs srs) r
                . whiskerR (appendPath sps sds) (appendPath ses sqs) sfs l
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

-- | Vertical composition.
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
(===) :: forall rs ss es fs ps qs gs. Sq rs ss es fs -> Sq ps qs fs gs -> Sq (ps +++ rs) (qs +++ ss) es gs
Sq top === Sq bot =
  withObAppend @Prof @ps @rs sps $
    withObAppend @Prof @qs @ss sqs $
      withAssoc @gs @qs @ss @Tight $
        withAssoc @ps @rs @es @Prof $
          withAssoc @ps @fs @ss @Prof $
            Sq $
              whiskerR (appendPath sps sfs) (appendPath sgs sqs) sss bot
                . whiskerL sps (appendPath srs ses) (appendPath sfs sss) top
  where
    sps :: SPath Prof ps
    sps = singPath
    sqs :: SPath Prof qs
    sqs = singPath
    srs :: SPath Prof rs
    srs = singPath
    sss :: SPath Prof ss
    sss = singPath
    ses :: SPath Prof es
    ses = weakenTight singPath
    sfs :: SPath Prof fs
    sfs = weakenTight singPath
    sgs :: SPath Prof gs
    sgs = weakenTight singPath

-- | Bend a vertical arrow in the companion direction.
--
-- > J--f--K
-- > |  v  |
-- > |  \->f
-- > |     |
-- > J-----J
toRight :: (Representable f) => Sq Nil (f ::: Nil) (f ::: Nil) Nil
toRight = Sq idN

-- | Bend a vertical arrow in the conjoint direction.
--
-- > J--f--K
-- > |  v  |
-- > f<-/  |
-- > |     |
-- > K-----K
toLeft :: forall f f'. (Proadjunction f f', Representable f) => Sq (f' ::: Nil) Nil (f ::: Nil) Nil
toLeft = Sq (counitNat @f @f')

-- | Bend a companion proarrow back to a vertical arrow.
--
-- > K-----K
-- > |     |
-- > f>-\  |
-- > |  v  |
-- > J--f--K
fromLeft :: (Representable f) => Sq (f ::: Nil) Nil Nil (f ::: Nil)
fromLeft = Sq idN

-- | Bend a conjoint proarrow back to a vertical arrow.
--
-- > J-----J
-- > |     |
-- > |  /-<f
-- > |  v  |
-- > J--f--K
fromRight :: forall f f'. (Proadjunction f f', Representable f) => Sq Nil (f' ::: Nil) Nil (f ::: Nil)
fromRight = Sq (unitNat @f @f')

unitNat :: forall p q. (Proadjunction p q) => Id :~> q :.: p
unitNat (Id f) = rmap f (Adj.unit @p @q) \\ f

counitNat :: forall p q. (Proadjunction p q) => p :.: q :~> Id
counitNat pq = Id (Adj.counit pq)

-- > K--I--K
-- > |  v  |
-- > |  @  |
-- > |     |
-- > K-----K
vUnitor :: forall k. (CategoryOf k) => Sq Nil Nil ((Id :: CAT k) ::: Nil) Nil
vUnitor = vSplitAll @Nil

-- > K-----K
-- > |     |
-- > |  @  |
-- > |  v  |
-- > K--I--K
vUnitorInv :: forall k. (CategoryOf k) => Sq Nil Nil Nil ((Id :: CAT k) ::: Nil)
vUnitorInv = vCombineAll @Nil

-- > I-f-g-K
-- > | v v |
-- > | \@/ |
-- > |  v  |
-- > I-gof-K
vCombine :: forall p q. (Representable p, Representable q) => Sq Nil Nil (p ::: q ::: Nil) (q :.: p ::: Nil)
vCombine = vCombineAll @(p ::: q ::: Nil)

-- > I-gof-K
-- > |  v  |
-- > | /@\ |
-- > | v v |
-- > I-f-g-K
vSplit :: forall p q. (Representable p, Representable q) => Sq Nil Nil (q :.: p ::: Nil) (p ::: q ::: Nil)
vSplit = vSplitAll @(p ::: q ::: Nil)

-- | Combine a whole bunch of vertical arrows into one composed arrow.
--
-- > J-p..-K
-- > | vvv |
-- > | \@/ |
-- > |  v  |
-- > J--f--K
vCombineAll :: forall ps. (IsTight ps) => Sq Nil Nil ps (Fold ps ::: Nil)
vCombineAll = withFoldRep tp (Sq idN)
  where
    tp :: SPath Tight ps
    tp = singPath

-- | Split one composed arrow into a whole bunch of vertical arrows.
--
-- > J--f--K
-- > |  v  |
-- > | /@\ |
-- > | vvv |
-- > J-p..-K
vSplitAll :: forall ps. (IsTight ps) => Sq Nil Nil (Fold ps ::: Nil) ps
vSplitAll = withFoldRep tp (Sq idN)
  where
    tp :: SPath Tight ps
    tp = singPath

-- | Combine a whole bunch of horizontal proarrows into one composed proarrow.
--
-- > K-----K
-- > p--\  |
-- > :--@--F
-- > :--/  |
-- > J-----J
hCombineAll :: forall ps. (IsPath ps) => Sq ps (Fold ps ::: Nil) Nil Nil
hCombineAll = withFoldOb sp (Sq idN)
  where
    sp :: SPath Prof ps
    sp = singPath

-- | Split one composed proarrow into a whole bunch of horizontal proarrows.
--
-- > K-----K
-- > |  /--p
-- > F--@--:
-- > |  \--:
-- > J-----J
hSplitAll :: forall ps. (IsPath ps) => Sq (Fold ps ::: Nil) ps Nil Nil
hSplitAll = withFoldOb sp (Sq idN)
  where
    sp :: SPath Prof ps
    sp = singPath

-- | The unit of an adjunction.
--
-- > J-------J
-- > |   /---q
-- > |   @   |
-- > |   \---p
-- > J-------J
unit :: forall p q. (Proadjunction p q) => Sq Nil (p ::: q ::: Nil) Nil Nil
unit = hCombineAll @Nil ||| hArr (unitNat @p @q) ||| hSplitAll @(p ::: q ::: Nil)

-- | The counit of an adjunction.
--
-- > K-------K
-- > p---\   |
-- > |   @   |
-- > q---/   |
-- > K-------K
counit :: forall p q. (Proadjunction p q) => Sq (q ::: p ::: Nil) Nil Nil Nil
counit = hCombineAll @(q ::: p ::: Nil) ||| hArr (counitNat @p @q) ||| hSplitAll @Nil

-- | Optics in the @Prof@ equipment.
--
-- > J-------J
-- > s>--@-->a
-- > |   @   |
-- > t<--@--<b
-- > K-------K
type EqpOptic a b s t = (IsOptic a b s t) => Sq (t ::: s ::: Nil) (b ::: a ::: Nil) Nil Nil

type IsOptic a b s t = (Representable s, Corepresentable t, Representable a, Corepresentable b)

mkOptic
  :: (IsOptic a b s t)
  => (forall x r. (Ob x) => (forall y. (Ob y) => (s % x ~> a % y) -> (b %% y ~> t %% x) -> r) -> r)
  -> EqpOptic a b s t
mkOptic k = Sq \((:.:) @x s t) -> s // k @x \ @y get put -> tabulate @_ @y (get . index s) :.: cotabulate (coindex t . put)

-- | Sequential composition of optics, with 2 holes.
seq
  :: forall a b s t a' b' u v
   . (Proadjunction u t, IsOptic a b s t, IsOptic a' b' u v)
  => EqpOptic a b s t -> EqpOptic a' b' u v -> Sq (v ::: s ::: Nil) (b' ::: a' ::: b ::: a ::: Nil) Nil Nil
seq st uv = (hId @s === unit @u @t === hId @v) ||| (st === uv)

data family Action :: (m, k) +-> k -> k -> m +-> k
instance (MonoidalAction act, Ob a) => FunctorForRep (Action act a :: m +-> k) where
  type Action act a @ x = Act act x a
  fmap f = actHom @act f (obj @a)

type ActionOptic act a b s t =
  EqpOptic (Rep (Action act a)) (Corep (Action act b)) (Rep (Action act s)) (Corep (Action act t))

fromOptic :: (MonoidalAction act, Ob a, Ob b, Ob s, Ob t) => ExOptic (ActFl act) a b s t -> ActionOptic act a b s t
fromOptic @act @a @b @s @t (ExOptic (l :: p s a) (r :: q b t)) = mkOptic \ @x k ->
  withActP @act @p @q l r \ @z f g ->
    withOb2 @_ @x @z $
      k @(x ** z)
        (multiplicatorInv @act @x @z @a . actHom @act (obj @x) f)
        (actHom @act (obj @x) g . multiplicator @act @x @z @b)

toOptic
  :: forall h x (s :: x +-> h) (t :: h +-> x) (a :: x +-> h) (b :: h +-> x)
   . (CategoryOf h, CategoryOf x, Representable s, Corepresentable t, Representable a, Corepresentable b)
  => EqpOptic a b s t
  -> ExOptic (ActFl (Rep Precomp)) a (CorepStar b) s (CorepStar t)
toOptic (Sq pl) =
  ExOptic
    (Rep @a @(ActionAt (Rep Precomp) (R (E (b :.: CorepStar t)))) (P.Prof get))
    (Corep @(CorepStar b) @(ActionAt (Rep Precomp) (R (E (b :.: CorepStar t)))) (P.Prof put))
  where
    get :: s :~> a :.: (b :.: CorepStar t)
    get s = s // case Adj.unit @(CorepStar t) @t of t :.: t' -> case pl (s :.: t) of a :.: b -> a :.: (b :.: t')

    put :: CorepStar b :.: (b :.: CorepStar t) :~> CorepStar t
    put (b' :.: (b :.: t')) = lmap (Adj.counit @(CorepStar b) @b (b' :.: b)) t'
