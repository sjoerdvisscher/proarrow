{-# LANGUAGE TupleSections #-}
module Proarrow.Promonad.Writer where

import Prelude (Monoid(..), (<>), fmap)

import Proarrow.Core (Promonad(..), Profunctor(..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Object.BinaryProduct ()

newtype Writer m a b = Writer { getWriter :: a -> (m, b) }

instance Profunctor (Writer m) where
  dimap l r (Writer f) = Writer (fmap r . f . l)

instance Monoid m => Promonad (Writer m) where
  id = Writer (mempty,)
  Writer g . Writer f = Writer \a -> case f a of (m1, b) -> case g b of (m2, c) -> (m1 <> m2, c)

instance Monoid m => MonoidalProfunctor (Writer m) where
  lift0 = id
  lift2 (Writer f) (Writer g) = Writer \(a1, a2) -> case f a1 of (m1, b1) -> case g a2 of (m2, b2) -> (m1 <> m2, (b1, b2))