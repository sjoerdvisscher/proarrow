module Proarrow.Profunctor.HaskValue where

import Data.Kind (Type)
import Prelude (Monoid (..), ($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (SelfAction, strongPar0)
import Proarrow.Category.Monoidal.Distributive (Cotraversable (..), Traversable (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Composition ((:.:) ((:.:)))

type HaskValue :: Type -> j +-> k
data HaskValue c a b where
  HaskValue :: (Ob a, Ob b) => c -> HaskValue c a b

instance (CategoryOf j, CategoryOf k) => Profunctor (HaskValue c :: j +-> k) where
  dimap l r (HaskValue c) = HaskValue c \\ l \\ r
  r \\ HaskValue{} = r

instance (Monoid c, CategoryOf k) => Promonad (HaskValue c :: k +-> k) where
  id = HaskValue mempty
  HaskValue c1 . HaskValue c2 = HaskValue (mappend c1 c2)

instance (Monoid c, Monoidal j, Monoidal k) => MonoidalProfunctor (HaskValue c :: j +-> k) where
  par0 = HaskValue mempty
  HaskValue @a1 @b1 c1 `par` HaskValue @a2 @b2 c2 = withOb2 @k @a1 @a2 $ withOb2 @j @b1 @b2 $ HaskValue (mappend c1 c2)

instance (SelfAction k) => Traversable (HaskValue c :: k +-> k) where
  traverse (HaskValue c :.: r) = strongPar0 :.: HaskValue c \\ r

instance (SelfAction k) => Cotraversable (HaskValue c :: k +-> k) where
  cotraverse (r :.: HaskValue c) = HaskValue c :.: strongPar0 \\ r
