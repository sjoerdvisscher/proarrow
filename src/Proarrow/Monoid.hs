module Proarrow.Monoid where

import Data.Kind (Type, Constraint)
import Prelude qualified as P

import Proarrow.Core (CategoryOf(..), Promonad(..), arr)
import Proarrow.Category.Monoidal (Monoidal(..))
import Proarrow.Object.BinaryProduct ((&&&), Cartesian)
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

class (Monoidal k, Ob c) => Comonoid (c :: k) where
  counit :: c ~> Unit
  comult :: c ~> c ** c