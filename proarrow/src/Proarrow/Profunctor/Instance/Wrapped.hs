-- | The 'Wrapped' newtype makes the values @p c m@ of a monoidal profunctor into 'Monoid's, for a comonoid
-- @c@ and a monoid @m@.
module Proarrow.Profunctor.Instance.Wrapped where

import Prelude qualified as P

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (Profunctor (..), Promonad (..))
import Proarrow.Monoid (Comonoid (..), Monoid)
import Proarrow.Monoid qualified as M
import Proarrow.Optic (PIso, iso)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Representable (..))

newtype Wrapped p a b = Wrapped {unWrapped :: p a b}
  deriving newtype (Profunctor, Promonad, MonoidalProfunctor, DaggerProfunctor, Representable, Corepresentable)

-- | Given as 'P.Semigroup'\/'P.Monoid' rather than as 'Proarrow.Monoid.Monoid' directly: at kind
-- @Type@ the latter comes from the blanket @'P.Monoid' m => 'Proarrow.Monoid.Monoid' (m :: Type)@
-- instance, so defining it here too would make every use overlap and solve to neither.
instance (Comonoid c, Monoid m, MonoidalProfunctor p) => P.Semigroup (Wrapped p c m) where
  l <> r = dimap comult M.mappend (l ** r)

instance (Comonoid c, Monoid m, MonoidalProfunctor p) => P.Monoid (Wrapped p c m) where
  mempty = dimap counit M.mempty one

wrapped :: PIso (p a b) (p a' b') (Wrapped p a b) (Wrapped p a' b')
wrapped = iso Wrapped unWrapped
