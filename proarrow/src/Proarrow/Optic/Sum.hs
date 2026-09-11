{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}

-- | Dual to 'Proarrow.Optic.Prod.ProdFl': combine over the /coproduct/ of two categories via
-- ':++:'. This lives in its own module (rather than next to 'Proarrow.Optic.Prod.ProdFl') only because
-- "Proarrow.Category.Instance.Coproduct" transitively imports "Proarrow.Optic" already (via
-- 'Proarrow.Profunctor.Corepresentable'), so 'Proarrow.Optic' can't import it back.
--
-- Unlike 'Proarrow.Optic.Prod.ProdFl', this doesn't let you combine two /different/ optics into one -- an
-- @(p ':++:' q) (L a) (L b)@ can only ever hold a @p@, never a @q@. Instead it lets any single
-- @w1@- or @w2@-flavored optic be /injected/ into a shared @'SumFl' w1 w2@ type, with the unused
-- side witnessed trivially by @'Id'@ (demanded via 'Flavor').
module Proarrow.Optic.Sum where

import Prelude (type (~))

import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), (:++:) (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), (\\), type (+->))
import Proarrow.Optic (FLAVOR, Flavor, Optic, Prostrong (..), legs2prof, withLegs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

-- | Unlike 'Proarrow.Optic.Prod.ProdFl', a 'SumFl' witness can be decomposed back: the trick is that
-- 'withSumL'\/'withSumR' only fix the /one/ endpoint anchored from outside (@s@ via @p@'s first
-- slot, @t@ via @q@'s second slot) -- the other endpoint (@a@, @b@) comes back /refined/ by the
-- continuation instead of being required upfront. That's what lets the ':.:' case recurse: the
-- existential "middle" object introduced there is exactly the next call's anchored endpoint, so
-- its tag is established by the previous step's own guarantee before it's ever needed as input.
type SumFl :: forall {j1} {k1} {j2} {k2}. FLAVOR j1 k1 -> FLAVOR j2 k2 -> FLAVOR (COPRODUCT j1 j2) (COPRODUCT k1 k2)
class SumFl w1 w2 (p :: COPRODUCT k1 k2 +-> COPRODUCT k1 k2) (q :: COPRODUCT j1 j2 +-> COPRODUCT j1 j2) where
  withSumL
    :: p (L s) a
    -> q b (L t)
    -> (forall p1 q1 a' b'. (w1 p1 q1, Profunctor p1, Profunctor q1, a ~ L a', b ~ L b') => p1 s a' -> q1 b' t -> r)
    -> r
  withSumR
    :: p (R s) a
    -> q b (R t)
    -> (forall p2 q2 a' b'. (w2 p2 q2, Profunctor p2, Profunctor q2, a ~ R a', b ~ R b') => p2 s a' -> q2 b' t -> r)
    -> r

instance
  (w1 p1 q1, w2 p2 q2, Profunctor p1, Profunctor p2, Profunctor q1, Profunctor q2)
  => SumFl w1 w2 (p1 :++: p2) (q1 :++: q2)
  where
  withSumL (InjL l1) (InjL r1) k = k l1 r1
  withSumR (InjR l2) (InjR r2) k = k l2 r2
instance
  (CategoryOf k1, CategoryOf k2, CategoryOf j1, CategoryOf j2, Flavor w1, Flavor w2)
  => SumFl w1 w2 (Id :: CAT (COPRODUCT k1 k2)) (Id :: CAT (COPRODUCT j1 j2))
  where
  withSumL (Id (InjL f)) (Id (InjL g)) k = k (Id f) (Id g)
  withSumR (Id (InjR f)) (Id (InjR g)) k = k (Id f) (Id g)
instance
  (SumFl w1 w2 f f', SumFl w1 w2 g g', Flavor w1, Flavor w2)
  => SumFl w1 w2 (f :.: g) (g' :.: f')
  where
  withSumL (f :.: g) (g' :.: f') k =
    withSumL @w1 @w2 f f' \p1 q1 ->
      withSumL @w1 @w2 g g' \p1' q1' ->
        k (p1 :.: p1') (q1' :.: q1)
  withSumR (f :.: g) (g' :.: f') k =
    withSumR @w1 @w2 f f' \p2 q2 ->
      withSumR @w1 @w2 g g' \p2' q2' ->
        k (p2 :.: p2') (q2' :.: q2)

injLOptic
  :: forall {j1} {k1} {j2} {k2} (w2 :: FLAVOR j2 k2) (w1 :: FLAVOR j1 k1) s t a b
   . (Flavor w1, w2 (Id :: CAT k2) (Id :: CAT j2), CategoryOf j1, CategoryOf k1, CategoryOf j2, CategoryOf k2)
  => Optic (Prostrong w1) s t a b -> Optic (Prostrong (SumFl w1 w2)) (L s) (L t) (L a) (L b)
injLOptic o =
  withLegs @w1 o \ @p @q l r ->
    legs2prof @(SumFl w1 w2)
      (InjL l :: (p :++: (Id :: CAT k2)) (L s) (L a))
      (InjL r :: (q :++: (Id :: CAT j2)) (L b) (L t))
      \\ l
      \\ r

injROptic
  :: forall {j1} {k1} {j2} {k2} (w1 :: FLAVOR j1 k1) (w2 :: FLAVOR j2 k2) s t a b
   . (Flavor w2, w1 (Id :: CAT k1) (Id :: CAT j1), CategoryOf j1, CategoryOf k1, CategoryOf j2, CategoryOf k2)
  => Optic (Prostrong w2) s t a b -> Optic (Prostrong (SumFl w1 w2)) (R s) (R t) (R a) (R b)
injROptic o =
  withLegs @w2 o \ @p @q l r ->
    legs2prof @(SumFl w1 w2)
      (InjR l :: ((Id :: CAT k1) :++: p) (R s) (R a))
      (InjR r :: ((Id :: CAT j1) :++: q) (R b) (R t))
      \\ l
      \\ r

-- | The inverse of 'injLOptic': every 'SumFl' witness of an @(L s) (L t) (L a) (L b)@-shaped
-- optic actually comes from an underlying @w1@-flavored optic on @s t a b@.
withSumOpticL
  :: forall {j1} {k1} {j2} {k2} (w1 :: FLAVOR j1 k1) (w2 :: FLAVOR j2 k2) s t a b r
   . (CategoryOf j1, CategoryOf k1, CategoryOf j2, CategoryOf k2, Flavor w1, Flavor w2, Ob a, Ob b)
  => Optic (Prostrong (SumFl w1 w2)) (L s) (L t) (L a) (L b)
  -> (Optic (Prostrong w1) s t a b -> r)
  -> r
withSumOpticL o k = withLegs @(SumFl w1 w2) o \l r -> withSumL @w1 @w2 l r \p1 q1 -> k (legs2prof @w1 p1 q1)

-- | The inverse of 'injROptic'.
withSumOpticR
  :: forall {j1} {k1} {j2} {k2} (w1 :: FLAVOR j1 k1) (w2 :: FLAVOR j2 k2) s t a b r
   . (CategoryOf j1, CategoryOf k1, CategoryOf j2, CategoryOf k2, Flavor w1, Flavor w2, Ob a, Ob b)
  => Optic (Prostrong (SumFl w1 w2)) (R s) (R t) (R a) (R b)
  -> (Optic (Prostrong w2) s t a b -> r)
  -> r
withSumOpticR o k = withLegs @(SumFl w1 w2) o \l r -> withSumR @w1 @w2 l r \p2 q2 -> k (legs2prof @w2 p2 q2)
