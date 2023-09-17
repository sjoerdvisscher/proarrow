module Proarrow.Promonad.Writer where

import Prelude (Monoid(..), (<>), fmap)

import Proarrow.Promonad (Promonad(..))
import Proarrow.Core (Category(..), Profunctor(..))
import Proarrow.Profunctor.Composition ((:.:)(..))

newtype Writer m a b = Writer { getWriter :: a -> (m, b) }

instance Profunctor (Writer m) where
  dimap l r (Writer f) = Writer (fmap r . f . l)

instance Monoid m => Promonad (Writer m) where
  unit f = Writer \a -> (mempty, f a)
  mult (Writer f :.: Writer g) = Writer \a -> case g a of (m1, b) -> case f b of (m2, c) -> (m1 <> m2, c)
