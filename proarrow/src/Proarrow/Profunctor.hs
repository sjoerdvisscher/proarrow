-- | The 'Profunctor' class and the profunctor kind @j +-> k@ (which unfolds to @k -> j -> Type@,
-- contravariant first per the math convention), re-exported from "Proarrow.Core". Profunctors are this
-- library's central generalization of functors.
module Proarrow.Profunctor
  ( type (+->)
  , Profunctor (..)
  , (//)
  ) where

import Proarrow.Core
