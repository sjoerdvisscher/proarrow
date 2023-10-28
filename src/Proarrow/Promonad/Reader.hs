module Proarrow.Promonad.Reader where

import Prelude (fmap, snd)

import Proarrow.Core (Promonad(..), Profunctor(..))

newtype Reader r a b = Reader { getReader :: (r, a) -> b }

instance Profunctor (Reader r) where
  dimap l r (Reader f) = Reader (r . f . fmap l)

instance Promonad (Reader r) where
  id = Reader snd
  Reader g . Reader f = Reader \(r, a) -> g (r, f (r, a))
