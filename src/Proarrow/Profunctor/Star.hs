{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Star where

import Data.Functor.Compose (Compose (..))
import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Sub (SUBCAT, Sub (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Category.Monoidal.Applicative (Alternative (..), Applicative (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (:~>), type (+->))
import Proarrow.Functor (Functor (..), Prelude (..))
import Proarrow.Object.BinaryCoproduct (COPROD (..), Cocartesian, Coprod (..), HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (Cartesian)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

type Star :: (k1 -> k2) -> k1 +-> k2
data Star f a b where
  Star :: (Ob b) => {unStar :: a ~> f b} -> Star f a b

instance (Functor f) => Profunctor (Star f) where
  dimap = dimapRep
  r \\ Star f = r \\ f

instance (Functor f) => Representable (Star f) where
  type Star f % a = f a
  index = unStar
  tabulate = Star
  repMap = map

instance (P.Monad m) => Promonad (Star (Prelude m)) where
  id = Star (Prelude . P.pure)
  Star g . Star f = Star \a -> Prelude (unPrelude (f a) P.>>= (unPrelude . g))

composeStar :: (Functor f) => Star f :.: Star g :~> Star (Compose f g)
composeStar (Star f :.: Star g) = Star (Compose . map g . f)

instance (Applicative f, Cartesian j, Cartesian k) => MonoidalProfunctor (Star (f :: j -> k)) where
  par0 = Star (pure id)
  Star @a f `par` Star @b g = let ab = obj @a `par` obj @b in Star (liftA2 @f @a @b ab . (f `par` g)) \\ ab

-- Hmm, another wrapper required...
type CoprodDom :: j +-> k -> COPROD j +-> k
data CoprodDom p a b where
  Co :: {unCo :: p a b} -> CoprodDom p a (COPR b)
instance (Profunctor p) => Profunctor (CoprodDom p) where
  dimap l (Coprod r) (Co p) = Co (dimap l r p)
  r \\ Co p = r \\ p

instance (Alternative f, Cartesian k, Cocartesian j) => MonoidalProfunctor (CoprodDom (Star (f :: j -> k))) where
  par0 = Co (Star empty)
  Co (Star @a f) `par` Co (Star @b g) = let ab = obj @a +++ obj @b in Co (Star (alt @f @a @b ab . (f `par` g))) \\ ab

instance (Functor (f :: Type -> Type)) => Strong Type (Star f) where
  act f (Star k) = Star (\(a, x) -> map (f a,) (k x))

instance (Functor f, P.Applicative f) => Strong (SUBCAT P.Traversable) (Star (Prelude f)) where
  act (Sub (Nat n)) (Star f) = Star (\t -> Prelude (P.traverse (unPrelude . f) (n t)))

strength :: forall {m} f a b. (Functor f, Strong m (Star f), Ob (a :: m), Ob b) => Act a (f b) ~> f (Act a b)
strength = unStar (act (obj @a) (Star (obj @(f b))))