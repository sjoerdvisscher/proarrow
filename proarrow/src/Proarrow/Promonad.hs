{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Promonads as effects: a 'Promonad' ("Proarrow.Core") that is 'Representable' is an ordinary 'Monad'
-- on objects ('return', 'bind'); a 'Promonad' that is 'Corepresentable' is a 'Comonad' ('extract',
-- 'extend'). Also 'Procomonad's and relative (co)monads ('RelativeMonad', 'RelativeComonad'). Concrete
-- promonads live in @Proarrow.Promonad.*@.
module Proarrow.Promonad
  ( Promonad (..)
  , Procomonad (..)
  , Monad
  , return
  , bind
  , Comonad
  , extract
  , extend
  , RelativeMonad (..)
  , RelAlgebra
  , RelativeComonad (..)
  , RelCoalgebra
  ) where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), src, (:~>), type (+->), type (~>))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))

type Procomonad :: k +-> k -> Constraint
class (Profunctor p) => Procomonad p where
  proextract :: p :~> (~>)
  produplicate :: p :~> p :.: p

instance (CategoryOf k) => Procomonad (Id :: CAT k) where
  proextract (Id f) = f
  produplicate (Id f) = Id (src f) :.: Id f

-- | A representable promonad is a monad on objects: it acts as the functor @m '%' -@, with
-- 'return' and 'bind'.
type Monad m = (Promonad m, Representable m)

-- | The unit of the monad @m@.
return :: forall m a. (Monad m, Ob a) => a ~> m % a
return = index @m id

-- | Kleisli extension: run a Kleisli arrow under @m@.
bind :: forall m b a. (Monad m, Ob b) => a ~> m % b -> m % a ~> m % b
bind f = index (tabulate @m @b f . (repUniv \\ f))

-- | Dually, a corepresentable promonad is a comonad on objects, acting as @w '%%' -@, with
-- 'extract' and 'extend'.
type Comonad w = (Promonad w, Corepresentable w)

-- | The counit of the comonad @w@.
extract :: forall w a. (Comonad w, Ob a) => w %% a ~> a
extract = coindex @w id

-- | CoKleisli extension: run a coKleisli arrow under @w@.
extend :: forall w a b. (Comonad w, Ob a) => w %% a ~> b -> w %% a ~> w %% b
extend f = coindex ((corepUniv \\ f) . cotabulate @w @a f)

type RelativeMonad :: i +-> k -> k +-> i -> Constraint
class (Representable m, Profunctor j) => RelativeMonad j m where
  relReturn :: (Ob a) => j a (m % a)
  relBind :: (Ob b) => j a (m % b) -> m % a ~> m % b

type RelAlgebra j m a b = j a b -> m % a ~> b

instance (Monad m) => RelativeMonad Id m where
  relReturn = Id (return @m)
  relBind @b (Id f) = bind @m @b f

type RelativeComonad :: i +-> k -> k +-> i -> Constraint
class (Corepresentable w, Profunctor j) => RelativeComonad j w where
  relExtract :: (Ob a) => j (w %% a) a
  relExtend :: (Ob a) => j (w %% a) b -> w %% a ~> w %% b

type RelCoalgebra j w a b = j a b -> a ~> w %% b

instance (Comonad w) => RelativeComonad Id w where
  relExtract = Id (extract @w)
  relExtend @a (Id f) = extend @w @a f
