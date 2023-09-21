module Proarrow.Promonad.Reader where

import Prelude (fmap, snd)

import Proarrow.Promonad (Promonad(..))
import Proarrow.Core (Category(..), Profunctor(..))
import Proarrow.Profunctor.Composition ((:.:)(..))

newtype Reader r a b = Reader { getReader :: (r, a) -> b }

instance Profunctor (Reader r) where
  dimap l r (Reader f) = Reader (r . f . fmap l)

instance Promonad (Reader r) where
  unit f = Reader (f . snd)
  mult (Reader f :.: Reader g) = Reader \(r, a) -> g (r, f (r, a))
