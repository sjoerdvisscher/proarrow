{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Optic.Grate where

import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..), first, second, swap, type (**))
import Proarrow.Category.Monoidal.Closed (Closed (..), Exp)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (CompactFlavor, ExOptic (..), FLAVOR, Optic, Optic_ (..), Prostrong (..), SubFlavor (..), ex2prof)
import Proarrow.Optic.Setter (SetterRes)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | A grate is a "residual lens" whose residual @m@ sits under an exponential rather than a
-- tensor: @s ~> (m ~~> a)@ and @(m ~~> b) ~> t@. Unlike a 'Proarrow.Optic.Traversal.Traversal',
-- this needs no 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor' machinery
-- at all -- 'zipWithP' is built directly out of 'Closed'\/'SymMonoidal' algebra
-- (curry\/apply\/swap), since we're manipulating morphisms directly rather than lifting an
-- arbitrary effect through a witness functor.
type GrateRes :: forall {k}. FLAVOR k k
class (SetterRes p q) => GrateRes (p :: k +-> k) (q :: k +-> k) where
  zipWithP
    :: forall s a b t
     . (Closed k, SymMonoidal k) => p s a -> q b t -> (forall (x :: k). (Ob x) => ((x ~~> a) ~> b) -> (x ~~> s) ~> t)

-- | Swap the argument order of a curried two-argument exponential: @x ~~> (m ~~> a) ~> m ~~> (x ~~> a)@.
flipExp
  :: forall {k} (x :: k) m a
   . (Closed k, SymMonoidal k, Ob x, Ob m, Ob a)
  => (x ~~> (m ~~> a)) ~> (m ~~> (x ~~> a))
flipExp =
  withObExp @k @m @a $
    withObExp @k @x @(m ~~> a) $
      withOb2 @k @(x ~~> (m ~~> a)) @m $
        curry @k @(x ~~> (m ~~> a)) @m
          ( curry @k @((x ~~> (m ~~> a)) ** m) @x
              ( apply @k @m @a
                  . first @m (apply @k @x @(m ~~> a))
                  . associatorInv @k @(x ~~> (m ~~> a)) @x @m
                  . second @(x ~~> (m ~~> a)) (swap @k @m @x)
                  . associator @k @(x ~~> (m ~~> a)) @m @x
              )
          )

instance (Closed k, SymMonoidal k, Ob m) => GrateRes (Rep (Exp m) :: k +-> k) (Corep (Exp m) :: k +-> k) where
  zipWithP @_ @a (Rep sm) (Corep mbt) @x kk = mbt . (kk ^^^ obj @m) . flipExp @x @m @a . (sm ^^^ obj @x)
instance (CategoryOf k) => GrateRes (Id :: k +-> k) (Id :: k +-> k) where
  zipWithP (Id l) (Id r) @x kk = r . kk . (l ^^^ obj @x)
instance (GrateRes f g, GrateRes f' g') => GrateRes (f :.: f') (g' :.: g) where
  zipWithP (f :.: f') (g' :.: g) @x kk = zipWithP @f @g f g @x (zipWithP @f' @g' f' g' @x kk)

instance CompactFlavor GrateRes

instance SubFlavor GrateRes SetterRes where subFlavor r = r

type Grate (s :: k) (t :: k) a b = Optic (Prostrong GrateRes) s t a b
type Grate' s a = Grate s s a a

-- | The eliminating carrier for grates: the polymorphic zipping function, as a profunctor in
-- @s@\/@t@.
type Grating :: forall {k}. k -> k -> k +-> k
data Grating a b s t where
  Grating
    :: (Ob s, Ob t)
    => (forall (x :: k). (Ob x) => ((x ~~> a) ~> b) -> (x ~~> s) ~> t) -> Grating (a :: k) b s t

instance (Closed k, SymMonoidal k, Ob (a :: k), Ob b) => Profunctor (Grating a b :: k +-> k) where
  dimap l r (Grating z) = (Grating \ @x kk -> r . z @x kk . (l ^^^ obj @x)) \\ l \\ r
  r \\ Grating{} = r

-- | Any flavor whose optics can zip has strength for the 'Grating' carrier.
instance
  (Closed k, SymMonoidal k, Ob (a :: k), Ob b, SubFlavor w GrateRes)
  => Prostrong (w :: FLAVOR k k) (Grating a b :: k +-> k)
  where
  proact @f @g (f@Objs :.: Grating z :.: g@Objs) =
    subFlavor @w @GrateRes @f @g (Grating \ @x kk -> zipWithP @f @g f g @x (z @x kk))

-- | Eliminate any grate-flavored optic to its zipping function, in either encoding.
withGrate
  :: forall {k} c (s :: k) (t :: k) a b r
   . (CategoryOf k, (Ob a, Ob b) => c (Grating a b))
  => Optic c s t a b -> ((forall (x :: k). (Ob x) => ((x ~~> a) ~> b) -> (x ~~> s) ~> t) -> r) -> r
withGrate (Optic l) k = case l @(Grating a b) (Grating \kk -> kk) of Grating z -> k (\ @x kk -> z @x kk)

-- | The canonical\/atomic grate constructor: the residual is the self-referential @s ~~> a@
-- (the "logarithm" of the get side), whose own get-map @m ~> (s ~~> a)@ trivializes to 'id' once
-- @m@ is fixed to be exactly @s ~~> a@.
grate
  :: forall {k} (s :: k) (t :: k) a b
   . (Closed k, SymMonoidal k, Ob s, Ob a, Ob b)
  => (((s ~~> a) ~~> b) ~> t) -> Grate s t a b
grate f@Objs =
  withObExp @k @s @a $
    let sa = curry @k @s @(s ~~> a) (apply @k @s @a . swap @k @s @(s ~~> a))
    in ex2prof
         (ExProstrong @(Rep (Exp (s ~~> a))) @(Corep (Exp (s ~~> a))) (Rep sa :.: ExIso id id :.: Corep f))
