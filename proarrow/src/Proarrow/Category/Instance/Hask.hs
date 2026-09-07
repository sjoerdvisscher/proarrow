-- | The category of Haskell types and functions: the 'Proarrow.Core.CategoryOf' structure on the kind 'Type',
-- with @(->)@ as the morphisms and every type an object. The instances themselves live next to
-- the classes they instantiate; this module just names the category.
module Proarrow.Category.Instance.Hask (Type, Hask) where

import Data.Kind (Type)

type Hask = (->)

-- Class instances of (->) are with the class definitions in order to avoid orphan instances
