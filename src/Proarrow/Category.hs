module Proarrow.Category
  ( CAT
  , CategoryOf (..)
  , dimapDefault
  , Supplies
  )
where

import Proarrow.Core
import Data.Kind (Constraint)

class (forall a. (Ob a) => c a) => k `Supplies` (c :: k -> Constraint)
instance (forall a. (Ob a) => c a) => k `Supplies` (c :: k -> Constraint)