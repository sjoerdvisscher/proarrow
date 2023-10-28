{-# LANGUAGE TupleSections #-}
module Proarrow.Promonad.Writer where

import Prelude (Monoid(..), (<>), fmap)

import Proarrow.Core (Promonad(..), Profunctor(..))

newtype Writer m a b = Writer { getWriter :: a -> (m, b) }

instance Profunctor (Writer m) where
  dimap l r (Writer f) = Writer (fmap r . f . l)

instance Monoid m => Promonad (Writer m) where
  id = Writer (mempty,)
  Writer g . Writer f = Writer \a -> case f a of (m1, b) -> case g b of (m2, c) -> (m1 <> m2, c)
