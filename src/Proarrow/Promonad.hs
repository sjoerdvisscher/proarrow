{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

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
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..))

type Procomonad :: k +-> k -> Constraint
class (Profunctor p) => Procomonad p where
  proextract :: p :~> (~>)
  produplicate :: p :~> p :.: p

instance (CategoryOf k) => Procomonad (Id :: CAT k) where
  proextract (Id f) = f
  produplicate (Id f) = Id (src f) :.: Id f

type Monad m = (Promonad m, Representable m)

return :: forall m a. (Monad m, Ob a) => a ~> m % a
return = index @m id

bind :: forall m b a. (Monad m, Ob b) => a ~> m % b -> m % a ~> m % b
bind f = index (tabulate @m @b f . (trivialRep \\ f))

type Comonad w = (Promonad w, Corepresentable w)

extract :: forall w a. (Comonad w, Ob a) => w %% a ~> a
extract = coindex @w id

extend :: forall w a b. (Comonad w, Ob a) => w %% a ~> b -> w %% a ~> w %% b
extend f = coindex ((trivialCorep \\ f) . cotabulate @w @a f)

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