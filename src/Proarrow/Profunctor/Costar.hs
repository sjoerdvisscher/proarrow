module Proarrow.Profunctor.Costar where

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>), (:~>))
import Proarrow.Functor (Functor(..))
import Proarrow.Profunctor.Corepresentable (Corepresentable(..))
import Proarrow.Profunctor.Composition ((:.:)(..))
import Data.Functor.Compose (Compose(..))

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

composeCostar :: Functor g => Costar f :.: Costar g :~> Costar (Compose g f)
composeCostar (Costar f :.: Costar g) = Costar (g . map f . getCompose)