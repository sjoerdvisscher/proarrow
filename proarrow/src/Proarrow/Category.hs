-- | Re-exports the kind-indexed category vocabulary from "Proarrow.Core" ('CAT', 'CategoryOf',
-- 'dimapDefault'), plus 'Supplies': @k \`Supplies\` c@ says that every object of the category @k@
-- satisfies the constraint @c@ (e.g. a 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' category
-- supplies 'Proarrow.Monoid.Comonoid').
module Proarrow.Category
  ( CAT
  , CategoryOf (..)
  , dimapDefault
  , Supplies
  )
where

import Data.Kind (Constraint)
import Proarrow.Core

class (forall a. (Ob a) => c a) => k `Supplies` (c :: k -> Constraint)
instance (forall a. (Ob a) => c a) => k `Supplies` (c :: k -> Constraint)
