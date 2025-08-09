module Proarrow.Profunctor.Wrapped where

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (Profunctor (..), Promonad (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Profunctor.Day (Day (..), DayUnit (..))
import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))

newtype Wrapped p a b = Wrapped {unWrapped :: p a b}

instance (Profunctor p) => Profunctor (Wrapped p) where
  dimap f g = Wrapped . dimap f g . unWrapped
  r \\ Wrapped p = r \\ p

instance (Promonad p) => Promonad (Wrapped p) where
  id = Wrapped id
  Wrapped f . Wrapped g = Wrapped (f . g)

instance (MonoidalProfunctor p) => MonoidalProfunctor (Wrapped p) where
  par0 = Wrapped par0
  Wrapped l `par` Wrapped r = Wrapped (l `par` r)

instance (DaggerProfunctor p) => DaggerProfunctor (Wrapped p) where
  dagger = Wrapped . dagger . unWrapped

instance (Comonoid c, Monoid m, MonoidalProfunctor p) => Monoid (Wrapped p c m) where
  mempty () = dimap counit mempty par0
  mappend (l, r) = dimap comult mappend (l `par` r)

instance (MonoidalProfunctor p) => Monoid (Wrapped p) where
  mempty = Prof \(DayUnit f g) -> Wrapped (dimap f g par0)
  mappend = Prof \(Day f (Wrapped p) (Wrapped q) g) -> Wrapped (dimap f g (p `par` q))

instance (Representable p) => Representable (Wrapped p) where
  type Wrapped p % a = p % a
  tabulate f = Wrapped (tabulate f)
  index (Wrapped p) = index p
  repMap = repMap @p

instance (Corepresentable p) => Corepresentable (Wrapped p) where
  type Wrapped p %% a = p %% a
  coindex (Wrapped p) = coindex p
  cotabulate f = Wrapped (cotabulate f)
  corepMap = corepMap @p