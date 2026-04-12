module Proarrow.Profunctor.Wrapped where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (Profunctor (..), Promonad (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Optic (Iso, iso)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Representable (..))

newtype Wrapped p a b = Wrapped {unWrapped :: p a b}
  deriving newtype (Profunctor, Promonad, MonoidalProfunctor, DaggerProfunctor, Representable, Corepresentable)

instance (Comonoid c, Monoid m, MonoidalProfunctor p) => Monoid (Wrapped p c m) where
  mempty () = dimap counit mempty par0
  mappend (l, r) = dimap comult mappend (l `par` r)

wrapped :: Iso (p a b) (p a' b') (Wrapped p a b) (Wrapped p a' b')
wrapped = iso Wrapped unWrapped