module Proarrow.Category.Instance.Hask (Type, Hask) where

import Data.Kind (Type)

type Hask = (->)

-- Class instances of (->) are with the class definitions in order to avoid orphan instances
