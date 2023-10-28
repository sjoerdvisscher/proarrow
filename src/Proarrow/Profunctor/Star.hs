module Proarrow.Profunctor.Star where

import Proarrow.Core (PRO, CategoryOf(..), Promonad(..), Profunctor(..), (:~>))
import Proarrow.Functor (Functor(..), Prelude(..))
import Proarrow.Profunctor.Representable (Representable(..))
import Proarrow.Profunctor.Composition ((:.:)(..))
import Data.Functor.Compose (Compose(..))
import qualified Prelude as P

type Star :: (k1 -> k2) -> PRO k2 k1
data Star f a b where
  Star :: Ob b => { getStar :: a ~> f b } -> Star f a b

instance Functor f => Profunctor (Star f) where
  dimap l r (Star f) = Star (map @f r . f . l) \\ r
  r \\ Star f = r \\ f

instance Functor f => Representable (Star f) where
  type Star f % a = f a
  index = getStar
  tabulate = Star
  repMap = map

instance P.Monad m => Promonad (Star (Prelude m)) where
  id = Star (Prelude . P.pure)
  Star g . Star f = Star \a -> Prelude (getPrelude (f a) P.>>= (getPrelude . g))

composeStar :: Functor f => Star f :.: Star g :~> Star (Compose f g)
composeStar (Star f :.: Star g) = Star (Compose . map g . f)