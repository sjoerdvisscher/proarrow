module Proarrow.Profunctor.Constant where

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Representable (Representable (..))

type Constant :: k -> j +-> k
data Constant c a b where
  Constant :: (Ob b) => a ~> c -> Constant c a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Constant c :: j +-> k) where
  dimap l r (Constant f) = Constant (f . l) \\ l \\ r
  r \\ Constant f = r \\ f

instance (CategoryOf j, CategoryOf k, Ob c) => Representable (Constant c :: j +-> k) where
  type Constant c % a = c
  index (Constant f) = f
  tabulate f = Constant f
  repMap _ = id