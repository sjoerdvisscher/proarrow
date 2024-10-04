module Proarrow.Profunctor.Star where

import Data.Functor.Compose (Compose (..))
import Prelude qualified as P

import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Applicative (Applicative (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (:~>), type (+->))
import Proarrow.Functor (Functor (..), Prelude (..))
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

-- instance (Alternative f, Cartesian k, Cocartesian j) => MonoidalProfunctor (Star (f :: j -> k)) where
--   par0 = Star empty
--   Star @a f `par` Star @b g = let ab = obj @a `par` obj @b in Star (alt @f @a @b ab . (f `par` g)) \\ ab