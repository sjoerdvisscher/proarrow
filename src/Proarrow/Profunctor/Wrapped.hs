module Proarrow.Profunctor.Wrapped where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (Iso, Profunctor (..), Promonad (..), iso)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Day (Day (..), DayUnit (..))
import Proarrow.Profunctor.Representable (Representable (..))

newtype Wrapped p a b = Wrapped {unWrapped :: p a b}
  deriving newtype (Profunctor, Promonad, MonoidalProfunctor, DaggerProfunctor, Representable, Corepresentable)

instance (Comonoid c, Monoid m, MonoidalProfunctor p) => Monoid (Wrapped p c m) where
  mempty () = dimap counit mempty par0
  mappend (l, r) = dimap comult mappend (l `par` r)

instance (MonoidalProfunctor p) => Monoid (Wrapped p) where
  mempty = Prof \(DayUnit f g) -> Wrapped (dimap f g par0)
  mappend = Prof \(Day f (Wrapped p) (Wrapped q) g) -> Wrapped (dimap f g (p `par` q))

wrapped :: Iso (p a b) (p a' b') (Wrapped p a b) (Wrapped p a' b')
wrapped = iso Wrapped unWrapped