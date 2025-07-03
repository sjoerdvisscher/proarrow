module Proarrow.Profunctor.Constant where

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep)

type Constant :: k -> j +-> k
data Constant c a b where
  Constant :: (Ob b) => a ~> c -> Constant c a b

instance (CategoryOf j, CategoryOf k, Ob c) => Profunctor (Constant c :: j +-> k) where
  dimap = dimapRep
  r \\ Constant f = r \\ f

instance (CategoryOf j, CategoryOf k, Ob c) => Representable (Constant c :: j +-> k) where
  type Constant c % a = c
  index (Constant f) = f
  tabulate f = Constant f
  repMap _ = id

type ConstIn :: j -> j +-> k
data ConstIn c a b where
  ConstIn :: (Ob a) => c ~> b -> ConstIn c a b

instance (CategoryOf j, CategoryOf k, Ob c) => Profunctor (ConstIn c :: j +-> k) where
  dimap = dimapCorep
  r \\ ConstIn f = r \\ f

instance (CategoryOf j, CategoryOf k, Ob c) => Corepresentable (ConstIn c :: j +-> k) where
  type ConstIn c %% a = c
  coindex (ConstIn f) = f
  cotabulate f = ConstIn f
  corepMap _ = id
