-- | The user-facing prelude: one import re-exporting the library's main surface -- categories, functors,
-- profunctors, promonads, objects, monoids, universal properties and the optics vocabulary
-- ("Proarrow.Optics"). For the core abstractions themselves ('CategoryOf', 'Promonad', 'Profunctor'),
-- start reading at "Proarrow.Core".
module Proarrow
  ( module Export
  , Promonad (..)
  ) where

import Proarrow.Category as Export
import Proarrow.Functor as Export
import Proarrow.Monoid as Export
import Proarrow.Object as Export
import Proarrow.Optics as Export
import Proarrow.Profunctor as Export
import Proarrow.Promonad (Promonad (..))
import Proarrow.Universal as Export
