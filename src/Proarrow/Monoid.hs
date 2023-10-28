{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Proarrow.Monoid where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Core (CategoryOf(..), Promonad(..), Profunctor (..), PRO, rmap)
import Proarrow.Category.Monoidal (MONOIDAL, Monoidal(..), Compose, Strictified(..))
import Proarrow.Object.BinaryProduct (ProductFunctor (..))
import Proarrow.Category.Instance.List (List(..), All)
import Proarrow.Object (obj)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Profunctor.Identity (Id(..))


class (Monoidal t, Ob m, CategoryOf k) => Monoid (t :: MONOIDAL k) (m :: k) where
  mempty :: t '[] '[m]
  mappend :: t '[m, m] '[m]
  mconcat :: forall ms. Ob ms => All ((~) m) ms => t ms '[m]
  mconcat = case obj @ms of
    Nil -> mempty
    Cons _ ms' -> mappend . (id @_ @'[m] `par` mconcat) \\ ms'

instance P.Monoid m => Monoid (Strictified ProductFunctor) (m :: Type) where
  mempty = Strictified \() -> P.mempty
  mappend = Strictified (P.uncurry (P.<>))

newtype AsMonoid p a b = AsMonoid { getAsMonoid :: p a b }
  deriving Profunctor
instance Promonad p => Monoid (Strictified Compose) (AsMonoid p :: PRO k k) where
  mempty = Strictified (Prof \(Id f) -> AsMonoid (rmap f id) \\ f)
  mappend = Strictified (Prof \(AsMonoid p :.: AsMonoid q) -> AsMonoid (q . p))
