module Proarrow.Profunctor.Costar where

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>))
import Proarrow.Functor (Functor(..))
import Proarrow.Profunctor.Corepresentable (Corepresentable(..))

type Costar :: (j -> k) -> PRO j k
data Costar f a b where
  Costar :: Ob a => { getCostar :: f a ~> b } -> Costar f a b

instance Functor f => Profunctor (Costar f) where
  dimap l r (Costar f) = Costar (r . f . map l) \\ l
  r \\ Costar f = r \\ f

instance Functor f => Corepresentable (Costar f) where
  type Costar f %% a = f a
  coindex = getCostar
  cotabulate = Costar
  corepMap = map
