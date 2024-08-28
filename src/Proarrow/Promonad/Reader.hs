module Proarrow.Promonad.Reader where

import Prelude (Monoid (..), fmap, snd, (<>))

import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (Profunctor (..), Promonad (..))
import Proarrow.Object.BinaryProduct ()
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Promonad (Procomonad (..))

newtype Reader r a b = Reader {unReader :: (r, a) -> b}

instance Profunctor (Reader r) where
  dimap l r (Reader f) = Reader (r . f . fmap l)

instance Promonad (Reader r) where
  id = Reader snd
  Reader g . Reader f = Reader \(r, a) -> g (r, f (r, a))

instance (Monoid m) => Procomonad (Reader m) where
  extract (Reader f) a = f (mempty, a)
  duplicate (Reader f) = Reader id :.: Reader \(m1, (m2, a)) -> f (m1 <> m2, a)

instance MonoidalProfunctor (Reader r) where
  par0 = id
  Reader f `par` Reader g = Reader \(r, (a, b)) -> (f (r, a), g (r, b))
