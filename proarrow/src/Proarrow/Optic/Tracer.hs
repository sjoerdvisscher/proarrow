{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __tracer__: the write-only optic whose residual sits on the /source and target/ side,
--
-- > Tracer s t a b = exists m. (m ** s ~> a, b ~> m ** t)
--
-- witnessed by 'Proarrow.Optic.Setter.CoTensorW'\/'Proarrow.Optic.Setter.TensorW' ('TracerRes' \/
-- 'withTracerP') -- a setter witness pair read the other way round, equivalently an 'ActRes'
-- @Tensor@ pair with the roles of the two witnesses swapped. Running it forwards closes a feedback loop through the
-- residual, so it distributes any 'Costrong' profunctor ('tracerP') and is a
-- 'Proarrow.Optic.Setter.Setter' exactly in a 'TracedMonoidal' category; run backwards
-- ('Proarrow.Optic.Setter.over' . 'Proarrow.Optic.re') it needs no trace at all. Build with
-- 'tracer', eliminate with 'tracerOf' (or 'Proarrow.Optic.Setter.over' at the hom) or recover the
-- legs with 'withTracer'; 'fromPTracer'\/'toPTracer' mediate with the profunctor-class-flavored
-- 'PTracer' (@'Optic' ('Costrong' 'Tensor')@).
module Proarrow.Optic.Tracer where

import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Tensor, type (**))
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( CompactFlavor
  , ExOptic (..)
  , FLAVOR
  , Flip
  , IsOptic (..)
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , SubFlavor (..)
  , convert
  , ex2prof
  , withLegs
  )
import Proarrow.Optic.Action (ActRes (..))
import Proarrow.Optic.Setter (CoTensorW (..), SetterRes (..), TensorW (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

-- | The tensor-action witness pair is an 'ActRes' @Tensor@ pair: @'TensorW' m@ is @'Proarrow.Profunctor.Representable.Rep'
-- ('Proarrow.Category.Monoidal.Action.ActionAt' Tensor m)@ and @'CoTensorW' m@ its 'Proarrow.Profunctor.Corepresentable.Corep'
-- in all but name.
instance (Monoidal k, Ob (m :: k)) => ActRes Tensor (TensorW m :: k +-> k) (CoTensorW m) where
  withActP (TensorW h) (CoTensorW i) k = k @m h i

-- | The tracer flavor: a witness pair whose legs are @m ** s ~> a@ and @b ~> m ** t@ for an
-- existential residual @m@ -- the residual functor is applied to the source and target rather
-- than to the foci, i.e. an @'ActRes' 'Tensor'@ pair with the roles of the two witnesses swapped.
-- 'withTracerP' recovers the legs (the 'Proarrow.Optic.MonoidalLens.withMonLensP' of tracers), and
-- distributing a 'Costrong' profunctor ('tracerP') is derived from them. This is the @'Prostrong'@
-- counterpart of @'Costrong' 'Tensor'@ the way 'Proarrow.Optic.MonoidalLens.MonLensRes' is of
-- @'Proarrow.Category.Monoidal.Strength.Strong' 'Tensor'@.
--
-- Every tracer witness pair is a setter pair ('SetterRes' superclass, so 'Proarrow.Optic.Setter.over',
-- 'Proarrow.Optic.Setter.set', '(Proarrow.Optic.Setter.%~)' all work) and its flip is one too
-- (@'SetterRes' q p@, so @'Proarrow.Optic.Setter.over' . 'Proarrow.Optic.re'@ works without a trace);
-- 'TracedMonoidal' rides in the instance context of the 'CoTensorW'\/'TensorW' witness, not in the
-- method, so ordinary setters keep their honest constraints. 'Monoidal' sits on the method rather
-- than the class so that the identity witness needs only 'CategoryOf' and 'Proarrow.Optic.Iso.IsoRes'
-- can include this flavor.
type TracerRes :: forall {k}. FLAVOR k k
class (SetterRes p q, SetterRes q p) => TracerRes (p :: k +-> k) (q :: k +-> k) where
  -- | Recover the two legs, with the residual @m@ existential.
  withTracerP
    :: (Monoidal k) => p s a -> q b t -> (forall (m :: k). (Ob m) => ((m ** s) ~> a) -> (b ~> (m ** t)) -> r) -> r

instance (CategoryOf k) => TracerRes (Id :: k +-> k) (Id :: k +-> k) where
  withTracerP (Id l) (Id r) k = k @Unit (l . leftUnitor) (leftUnitorInv . r) \\ l \\ r

instance
  forall k (f :: k +-> k) (f' :: k +-> k) (g :: k +-> k) (g' :: k +-> k)
   . (TracerRes f g, TracerRes f' g')
  => TracerRes (f :.: f') (g' :.: g)
  where
  withTracerP ((f :: f s x) :.: f') (g' :.: (g :: g y t)) kk =
    withTracerP f g \ @(mo :: k) ho io ->
      withTracerP f' g' \ @(mi :: k) hi ii ->
        withOb2 @k @mi @mo
          ( kk @(mi ** mo)
              (hi . (obj @mi ** ho) . associator @k @mi @mo @s)
              (associatorInv @k @mi @mo @t . (obj @mi ** io) . ii)
          )
          \\ f
          \\ g

-- | The tracer witness: 'CoTensorW' on the left, 'TensorW' on the right. Its 'overP' is the trace
-- of @m ** s ~> a ~> b ~> m ** t@ over @m@, so it needs the category to be 'TracedMonoidal'.
instance (TracedMonoidal k, Ob (m :: k)) => SetterRes (CoTensorW m :: k +-> k) (TensorW m) where
  overP (CoTensorW l) (TensorW r) f = coact @Tensor @_ @m (r . f . l)

instance (TracedMonoidal k, Ob (m :: k)) => TracerRes (CoTensorW m :: k +-> k) (TensorW m) where
  withTracerP (CoTensorW l) (TensorW r) k = k @m l r

-- | Distribute any 'Costrong' profunctor through a tracer witness pair: 'dimap' the legs on and
-- 'coact' the residual away. At the hom this is 'overP'.
tracerP
  :: forall {k} p q (s :: k) a b t r
   . (TracerRes p q, Costrong Tensor r)
  => p s a -> q b t -> r a b -> r s t
tracerP l r rab = withTracerP l r (\ @m i h -> coact @Tensor @r @m (dimap i h rab)) \\ l \\ r

instance CompactFlavor TracerRes

instance SubFlavor TracerRes SetterRes where subFlavor r = r

-- | A reversed tracer is still a setter (run it with 'Proarrow.Optic.Setter.over' . 'Proarrow.Optic.re').
instance SubFlavor (Flip TracerRes) SetterRes where subFlavor r = r

-- | A tracer is a reversed setter: its witnesses are a setter's read the other way round, so
-- @'convert' t :: 'Optic' ('Prostrong' ('Flip' 'SetterRes')) s t a b@. The converse fails -- a
-- flipped setter need not have a trace (e.g. a flipped lens witness) -- so tracers are the
-- subflavor of flipped setters that can also run /forwards/.
instance SubFlavor TracerRes (Flip SetterRes) where subFlavor r = r

type Tracer (s :: k) (t :: k) a b = Optic (Prostrong TracerRes) s t a b
type Tracer' s a = Tracer s s a a

-- | Build a tracer from its two legs and a chosen residual @m@: @m ** s ~> a@ decomposes the source
-- (given the residual), @b ~> m ** t@ rebuilds the target and produces the residual to feed back.
tracer
  :: forall {k} (m :: k) (s :: k) t a b
   . (TracedMonoidal k, Ob m, Ob s, Ob t, Ob a, Ob b)
  => ((m ** s) ~> a) -> (b ~> (m ** t)) -> Tracer s t a b
tracer l r = ex2prof (ExProstrong @(CoTensorW m) @(TensorW m) (CoTensorW l :.: ExIso id id :.: TensorW r))

-- | Distribute any 'Costrong' profunctor through a tracer (or any stronger optic). At the hom this
-- is 'Proarrow.Optic.Setter.over', computing the feedback loop through the residual.
--
-- Accepts any encoding (cf. 'Proarrow.Optic.Traversal.traverseOf'): a 'PTracer' works directly, as
-- does a '(Proarrow.Optic.%)'-composite.
tracerOf
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, Costrong Tensor r, (Ob a, Ob b) => c (ExOptic TracerRes a b))
  => Optic c s t a b -> r a b -> r s t
tracerOf o rab = withLegs (\l r -> tracerP l r rab) (convert @c @TracerRes o)

-- | The eliminating carrier for tracers: the two legs with the residual @m@ existential (the
-- 'Proarrow.Optic.MonoidalLens.MonShop' of tracers).
type Tracing :: forall {k}. k -> k -> k +-> k
data Tracing a b s t where
  Tracing :: (Ob a, Ob b, Ob m, Ob s, Ob t) => ((m ** s) ~> a) -> (b ~> (m ** t)) -> Tracing a b s t

instance (Monoidal k, Ob (a :: k), Ob b) => Profunctor (Tracing a b :: k +-> k) where
  dimap l r (Tracing @_ @_ @m h i) = Tracing @a @b @m (h . (obj @m ** l)) ((obj @m ** r) . i) \\ l \\ r
  r \\ Tracing{} = r

-- | Any flavor whose optics have tracer legs has strength for the 'Tracing' carrier: absorbing a
-- witness pair tensors its residual onto the carrier's.
instance (Monoidal k, Ob (a :: k), Ob b, SubFlavor w TracerRes) => Prostrong (w :: FLAVOR k k) (Tracing a b :: k +-> k) where
  proact @f @g @s @t (f@Objs :.: Tracing @_ @_ @m h i :.: g@Objs) =
    subFlavor @w @TracerRes @f @g
      ( withTracerP f g \ @mf hf ir ->
          withOb2 @k @m @mf
            ( Tracing @a @b @(m ** mf)
                (h . (obj @m ** hf) . associator @k @m @mf @s)
                (associatorInv @k @m @mf @t . (obj @m ** ir) . i)
            )
      )

-- | 'Tracing' is the free 'Costrong' profunctor on the legs, so profunctor-class tracers eliminate
-- through it too.
instance (Monoidal k, Ob (a :: k), Ob b) => Costrong Tensor (Tracing a b :: k +-> k) where
  coact @m @x @y (Tracing @_ @_ @m' h i) =
    withOb2 @k @m' @m (Tracing @a @b @(m' ** m) (h . associator @k @m' @m @x) (associatorInv @k @m' @m @y . i))

-- | Eliminate any optic that is at least an iso and at most a tracer to its two legs, recovering
-- the existential residual @m@, in either encoding.
withTracer
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, (Ob a, Ob b) => c (Tracing a b))
  => Optic c s t a b -> (forall (m :: k). (Ob m) => ((m ** s) ~> a) -> (b ~> (m ** t)) -> r) -> r
withTracer (Optic l) k = case l @(Tracing a b) (Tracing @a @b @Unit leftUnitor leftUnitorInv) of
  Tracing @_ @_ @m h i -> k @m h i

-- | A tracer in the profunctor-class-flavored encoding (cf. 'Proarrow.Optic.PIso'). Equivalent to
-- 'Tracer' via 'toPTracer' and 'fromPTracer'.
type PTracer s t a b = Optic (Costrong Tensor) s t a b

instance IsOptic (Costrong Tensor) where withProfunctor r = r

-- | The free tracer profunctor @'ExOptic' 'TracerRes' a b@ is 'Costrong': absorbing the residual @m@
-- is one more 'CoTensorW'\/'TensorW' layer, mirroring @'Proarrow.Category.Monoidal.Strength.Strong' 'Tensor' ('ExOptic' 'Proarrow.Optic.Traversal.MonTravRes' a b)@.
instance (TracedMonoidal k, Ob (a :: k), Ob b) => Costrong Tensor (ExOptic TracerRes a b :: k +-> k) where
  coact @m @x @y e =
    withOb2 @k @m @x $
      withOb2 @k @m @y $
        ExProstrong @(CoTensorW m) @(TensorW m) (CoTensorW id :.: e :.: TensorW id)

-- | Instantiate a profunctor-class tracer at the free tracer profunctor (the Pastro-Street move).
fromPTracer :: forall {k} (s :: k) (t :: k) a b. (TracedMonoidal k) => PTracer s t a b -> Tracer s t a b
fromPTracer = convert

-- | Eliminate a 'Tracer' to its profunctor-class form: run 'tracerP' at the caller's profunctor.
toPTracer :: forall {k} (s :: k) (t :: k) a b. (CategoryOf k) => Tracer s t a b -> PTracer s t a b
toPTracer = withLegs \l@Objs r@Objs -> Optic (tracerP l r)
