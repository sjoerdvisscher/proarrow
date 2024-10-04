module Proarrow.Profunctor.Costar where

import Control.Monad qualified as P
import Data.Functor.Compose (Compose (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (:~>), type (+->))
import Proarrow.Functor (Functor (..), Prelude (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep)
import Proarrow.Promonad (Procomonad (..))
import Prelude qualified as P

type Costar :: (j -> k) -> k +-> j
data Costar f a b where
  Costar :: (Ob a) => {unCostar :: f a ~> b} -> Costar f a b

instance (Functor f) => Profunctor (Costar f) where
  dimap = dimapCorep
  r \\ Costar f = r \\ f

instance (Functor f) => Corepresentable (Costar f) where
  type Costar f %% a = f a
  coindex = unCostar
  cotabulate = Costar
  corepMap = map

instance (P.Monad m) => Procomonad (Costar (Prelude m)) where
  extract (Costar f) = f . Prelude . P.pure
  duplicate (Costar f) = Costar unPrelude :.: Costar (f . Prelude . P.join . unPrelude)

composeCostar :: (Functor g) => Costar f :.: Costar g :~> Costar (Compose g f)
composeCostar (Costar f :.: Costar g) = Costar (g . map f . getCompose)
