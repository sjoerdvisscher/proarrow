module Proarrow.Monoid where

import Data.Kind (Type, Constraint)
import Prelude qualified as P

import Proarrow.Core (CategoryOf(..), Promonad(..), arr)
import Proarrow.Category.Monoidal (Monoidal(..))
import Proarrow.Object.BinaryProduct ((&&&), Cartesian)
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Category.Bicategory.Prof (Prof(..), PROFK, ProfK(PK))
import Proarrow.Category.Monoidal.Endo (Endo(..), ENDO (E))
import Proarrow.Object.Terminal (terminate)


type Monoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob m) => Monoid (m :: k) where
  mempty :: Unit ~> m
  mappend :: m ** m ~> m

instance P.Monoid m => Monoid (m :: Type) where
  mempty () = P.mempty
  mappend = P.uncurry (P.<>)

newtype GenElt x m = GenElt (x ~> m)

instance (Monoid m, Cartesian k) => P.Semigroup (GenElt x (m :: k)) where
  GenElt f <> GenElt g = GenElt (mappend . (f &&& g))
instance (Monoid m, Cartesian k, Ob x) => P.Monoid (GenElt x (m :: k)) where
  mempty = GenElt (mempty . arr terminate)

instance Promonad p => Monoid (E (PK p) :: ENDO PROFK k) where
  mempty = Endo (Prof arr)
  mappend = Endo (Prof \(p :.: q) -> q . p)
