{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Profunctor.Costar where

import Control.Monad qualified as P
import Data.Functor.Compose (Compose (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (:~>), type (+->), (//), rmap, obj)
import Proarrow.Functor (Functor (..), Prelude (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep)
import Proarrow.Promonad (Procomonad (..))
import Prelude qualified as P
import Proarrow.Category.Monoidal (MonoidalProfunctor (..), withOb2)
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..))
import Proarrow.Category.Monoidal.Distributive (Traversable (..), Cotraversable (..))
import Proarrow.Profunctor.Star (Star (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Category.Enriched.ThinCategory (ThinProfunctor (..), Discrete, Thin, withEq)

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

-- | Every functor between cartesian categories is a colax monoidal functor.
instance (Cartesian j, Cartesian k, Functor (f :: j -> k)) => MonoidalProfunctor (Costar f) where
  par0 = Costar terminate
  Costar @a f `par` Costar @b g = withOb2 @j @a @b (Costar (f . map (fst @j @a @b) &&& g . map (snd @j @a @b)))

instance (Functor t, Traversable (Star t)) => Cotraversable (Costar t) where
  cotraverse (p :.: Costar f) = p // Costar id :.: case traverse (Star id :.: p) of p' :.: Star g -> rmap (f . g) p'

instance (Functor f, Discrete j, Thin k) => ThinProfunctor (Costar f :: j +-> k) where
  type HasArrow (Costar f) a b = f a P.~ b
  arr = Costar id
  withArr (Costar f) = withEq f

costrength :: forall {m} f a b. (Functor f, Strong m (Costar f), Ob (a :: m), Ob b) => f (Act a b) ~> Act a (f b)
costrength = unCostar (act (obj @a) (Costar (obj @(f b))))