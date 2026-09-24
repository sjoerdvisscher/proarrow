{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __tracer__: the write-only optic whose residual sits on the source and target side,
--
-- > Tracer s t a b = exists m. (m ** s ~> a, b ~> m ** t)
--
-- witnessed by @'Corep'@\/@'Rep'@ @('ActionAt' 'Tensor' m)@ ('TracerFl'), a setter witness pair
-- read the other way round. Running it forwards closes a feedback loop through the residual, so it
-- distributes any 'Costrong' profunctor ('tracerP') and is a 'Proarrow.Optic.Setter.Setter'
-- exactly in a 'TracedMonoidal' category. Run backwards
-- ('Proarrow.Optic.Setter.over' . 'Proarrow.Optic.re') it needs no trace. Build with 'tracer',
-- eliminate with 'tracerOf' or recover the legs with 'withTracer'. 'fromPTracer'\/'toPTracer'
-- mediate with 'PTracer' (@'Optic' ('Costrong' 'Tensor')@).
module Proarrow.Optic.Tracer where

import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Tensor, type (**))
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic (..)
  , FLAVOR
  , Flavor
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , convert
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.Setter (SetterFl (..))
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..))

-- | The tracer flavor: a witness pair with legs @m ** s ~> a@ and @b ~> m ** t@ for an
-- existential residual @m@, an @'ActFl' 'Tensor'@ pair with the witnesses' roles swapped. It is
-- the @'Prostrong'@ counterpart of @'Costrong' 'Tensor'@, as
-- 'Proarrow.Optic.MonoidalLens.MonLensFl' is of
-- @'Proarrow.Category.Monoidal.Strength.Strong' 'Tensor'@.
--
-- A tracer pair and its flip are both setter pairs, so 'Proarrow.Optic.Setter.over' works on a
-- tracer and on its 'Proarrow.Optic.re', and
-- @'convert' t :: 'Optic' ('Prostrong' ('Flip' 'SetterFl')) s t a b@ typechecks. The converse
-- fails: a flipped setter (e.g. a flipped lens witness) need not have a trace.
--
-- 'TracedMonoidal' sits in the instance context of the tensor-action witness, so ordinary setters
-- don't pick up the constraint. 'Monoidal' sits on the method so that the identity witness needs
-- only 'CategoryOf' and 'Proarrow.Optic.Iso.IsoFl' can include this flavor.
type TracerFl :: forall {k}. FLAVOR k k
class (SetterFl p q, SetterFl q p) => TracerFl (p :: k +-> k) (q :: k +-> k) where
  -- | Recover the two legs, with the residual @m@ existential.
  withTracerP
    :: (Monoidal k) => p s a -> q b t -> (forall (m :: k). (Ob m) => ((m ** s) ~> a) -> (b ~> (m ** t)) -> r) -> r

instance (CategoryOf k) => TracerFl (Id :: k +-> k) (Id :: k +-> k) where
  withTracerP (Id l) (Id r) k = k @Unit (l . leftUnitor) (leftUnitorInv . r) \\ l \\ r

instance
  forall k (f :: k +-> k) (f' :: k +-> k) (g :: k +-> k) (g' :: k +-> k)
   . (TracerFl f g, TracerFl f' g')
  => TracerFl (f :.: f') (g' :.: g)
  where
  withTracerP ((f@Objs :: f s x) :.: f') (g' :.: (g@Objs :: g y t)) kk =
    withTracerP f g \ @(mo :: k) ho io ->
      withTracerP f' g' \ @(mi :: k) hi ii ->
        withOb2 @k @mi @mo
          ( kk @(mi ** mo)
              (hi . (obj @mi ** ho) . associator @k @mi @mo @s)
              (associatorInv @k @mi @mo @t . (obj @mi ** io) . ii)
          )

-- | The tracer witness: the tensor-action pair read the other way round, @'Corep' ('ActionAt' 'Tensor' m)@
-- on the left and @'Rep' ('ActionAt' 'Tensor' m)@ on the right. Its 'overP' is the trace
-- of @m ** s ~> a ~> b ~> m ** t@ over @m@, so it needs the category to be 'TracedMonoidal'.
instance (TracedMonoidal k, Ob (m :: k)) => SetterFl (Corep (ActionAt Tensor m) :: k +-> k) (Rep (ActionAt Tensor m)) where
  overP (Corep l) (Rep r) f = coact @Tensor @_ @m (r . f . l)

instance (TracedMonoidal k, Ob (m :: k)) => TracerFl (Corep (ActionAt Tensor m) :: k +-> k) (Rep (ActionAt Tensor m)) where
  withTracerP (Corep l) (Rep r) k = k @m l r

-- | Distribute any 'Costrong' profunctor through a tracer witness pair: 'dimap' the legs on and
-- 'coact' the residual away. At the hom this is 'overP'.
tracerP
  :: forall {k} p q (s :: k) a b t r
   . (TracerFl p q, Costrong Tensor r)
  => p s a -> q b t -> r a b -> r s t
tracerP l r rab = withTracerP l r (\ @m i h -> coact @Tensor @r @m (dimap i h rab)) \\ l \\ r

type Tracer (s :: k) (t :: k) a b = Optic (Prostrong TracerFl) s t a b
type Tracer' s a = Tracer s s a a

-- | Build a tracer from its two legs and a chosen residual @m@: @m ** s ~> a@ decomposes the source
-- (given the residual), @b ~> m ** t@ rebuilds the target and produces the residual to feed back.
tracer
  :: forall {k} (m :: k) (s :: k) t a b
   . (TracedMonoidal k, Ob m, Ob s, Ob t, Ob a, Ob b)
  => ((m ** s) ~> a) -> (b ~> (m ** t)) -> Tracer s t a b
tracer l r = legs2prof @TracerFl (Corep @s @(ActionAt Tensor m) l) (Rep @t @(ActionAt Tensor m) r)

-- | Distribute any 'Costrong' profunctor through a tracer (or any stronger optic). At the hom this
-- is 'Proarrow.Optic.Setter.over', computing the feedback loop through the residual.
--
-- Accepts any encoding (cf. 'Proarrow.Optic.Traversal.traverseOf'): a 'PTracer' works directly, as
-- does a '(Proarrow.Optic.%)'-composite.
tracerOf
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, Costrong Tensor r, c (ExOptic TracerFl a b))
  => Optic c s t a b -> r a b -> r s t
tracerOf o rab = withLegs @TracerFl o \l r -> tracerP l r rab

-- | The generic carrier absorbs the residual of a 'Costrong' action whenever the flavor contains the
-- tracer generator: one more tensor-action layer, composed onto the witnesses.
-- With it, profunctor-class-flavored tracers ('PTracer') eliminate through 'ExOptic' too.
instance
  ( Monoidal k
  , Ob (a :: k)
  , Ob b
  , Flavor w
  , forall (m :: k). (Ob m) => w (Corep (ActionAt Tensor m)) (Rep (ActionAt Tensor m))
  )
  => Costrong Tensor (ExOptic w a b :: k +-> k)
  where
  coact @m @x @y (ExOptic @p @q l r) =
    withOb2 @k @m @x $
      withOb2 @k @m @y $
        ExOptic @(Corep (ActionAt Tensor m) :.: p) @(q :.: Rep (ActionAt Tensor m)) (corepUniv :.: l) (r :.: repUniv)

-- | Eliminate any optic that is at least an iso and at most a tracer to its two legs, recovering
-- the existential residual @m@, in either encoding: run it at its witness pair ('ExOptic' 'TracerFl',
-- via 'withLegs') and read the legs off with 'withTracerP'.
withTracer
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, (Ob a, Ob b) => c (ExOptic TracerFl a b))
  => Optic c s t a b -> (forall (m :: k). (Ob m) => ((m ** s) ~> a) -> (b ~> (m ** t)) -> r) -> r
withTracer o k = withLegs @TracerFl o \ @p @q p q -> withTracerP @p @q p q \ @m h i -> k @m h i

-- | A tracer in the profunctor-class-flavored encoding (cf. 'Proarrow.Optic.PIso'). Equivalent to
-- 'Tracer' via 'toPTracer' and 'fromPTracer'.
type PTracer s t a b = Optic (Costrong Tensor) s t a b

-- | Instantiate a profunctor-class tracer at the generic carrier @'ExOptic' 'TracerFl' a b@, which is
-- 'Costrong' by the instance above (the Pastro-Street move).
fromPTracer :: forall {k} (s :: k) (t :: k) a b. (TracedMonoidal k) => PTracer s t a b -> Tracer s t a b
fromPTracer = convert

-- | Eliminate a 'Tracer' to its profunctor-class form: run 'tracerP' at the caller's profunctor.
toPTracer :: forall {k} (s :: k) (t :: k) a b. (CategoryOf k) => Tracer s t a b -> PTracer s t a b
toPTracer o = withLegs @TracerFl o \l@Objs r@Objs -> Optic (tracerP l r)
