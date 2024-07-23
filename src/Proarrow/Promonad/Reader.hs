module Proarrow.Promonad.Reader where

import Prelude (Monoid(..), (<>), fmap, snd)

import Proarrow.Core (Promonad(..), Profunctor(..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Object.BinaryProduct ()
import Proarrow.Promonad (Procomonad(..))
import Proarrow.Profunctor.Composition ((:.:)(..))

newtype Reader r a b = Reader { getReader :: (r, a) -> b }

instance Profunctor (Reader r) where
  dimap l r (Reader f) = Reader (r . f . fmap l)

instance Promonad (Reader r) where
  id = Reader snd
  Reader g . Reader f = Reader \(r, a) -> g (r, f (r, a))

instance Monoid m => Procomonad (Reader m) where
  extract (Reader f) a = f (mempty, a)
  duplicate (Reader f) = Reader id :.: Reader \(m1, (m2, a)) -> f (m1 <> m2, a)

instance MonoidalProfunctor (Reader r) where
  lift0 = id
  lift2 (Reader f) (Reader g) = Reader \(r, (a, b)) -> (f (r, a), g (r, b))