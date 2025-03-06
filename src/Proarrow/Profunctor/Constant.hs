module Proarrow.Profunctor.Constant where

import Data.Kind (Type)
import Prelude (Monoid (..), ($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (SelfAction, strongPar0)
import Proarrow.Category.Monoidal.Distributive (Cotraversable (..), Traversable (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Composition ((:.:) ((:.:)))

type Constant :: Type -> j +-> k
data Constant c a b where
  Constant :: (Ob a, Ob b) => c -> Constant c a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Constant c :: j +-> k) where
  dimap l r (Constant c) = Constant c \\ l \\ r
  r \\ Constant{} = r

instance (Monoid c, CategoryOf k) => Promonad (Constant c :: k +-> k) where
  id = Constant mempty
  Constant c1 . Constant c2 = Constant (mappend c1 c2)

instance (Monoid c, Monoidal j, Monoidal k) => MonoidalProfunctor (Constant c :: j +-> k) where
  par0 = Constant mempty
  Constant @a1 @b1 c1 `par` Constant @a2 @b2 c2 = withOb2 @k @a1 @a2 $ withOb2 @j @b1 @b2 $ Constant (mappend c1 c2)

instance (SelfAction k) => Traversable (Constant c :: k +-> k) where
  traverse (Constant c :.: r) = strongPar0 :.: Constant c \\ r

instance (SelfAction k) => Cotraversable (Constant c :: k +-> k) where
  cotraverse (r :.: Constant c) = Constant c :.: strongPar0 \\ r
