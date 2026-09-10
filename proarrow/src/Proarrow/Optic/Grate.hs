{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __grate__: the closed-category optic whose residual sits under an exponential,
--
-- > Grate s t a b = exists m. (s ~> (m ~~> a), (m ~~> b) ~> t)
--
-- witnessed by @'Rep'@\/@'Corep'@ @('Exp' m)@ ('GrateRes' \/ 'zipWithP'). It subtypes only to
-- 'Proarrow.Optic.Setter.Setter', and every 'Proarrow.Optic.Kaleidoscope.Kaleidoscope' is one.
-- Build with 'grate' (whose residual is the \"logarithm\" @s ~~> a@), eliminate to the zipping
-- function with 'withGrate', via the generic 'ExOptic' carrier.
module Proarrow.Optic.Grate where

import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..), first, second, swap, type (**))
import Proarrow.Category.Monoidal.Closed (Closed (..), Exp)
import Proarrow.Core (CategoryOf (..), Promonad (..), obj, type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Optic
  , Prostrong (..)
  , SubFlavor (..)
  , legs2prof
  , withLegs
  )
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

instance SubFlavor GrateRes SetterRes where subFlavor r = r

type Grate (s :: k) (t :: k) a b = Optic (Prostrong GrateRes) s t a b
type Grate' s a = Grate s s a a

-- | Eliminate any grate-flavored optic to its zipping function, in either encoding: run it at its
-- witness pair ('ExOptic' 'GrateRes', via 'withLegs') and read the zipper off with 'zipWithP'.
withGrate
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Closed k, SymMonoidal k, (Ob a, Ob b) => c (ExOptic GrateRes a b))
  => Optic c s t a b -> ((forall (x :: k). (Ob x) => ((x ~~> a) ~> b) -> (x ~~> s) ~> t) -> r) -> r
withGrate o k = withLegs @GrateRes o \ @p @q p q -> k (\ @x kk -> zipWithP @p @q p q @x kk)

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
    in legs2prof @GrateRes (Rep @a @(Exp (s ~~> a)) sa) (Corep @b @(Exp (s ~~> a)) f)
