module Proarrow.Object (
  Obj,
  obj,
  src,
  tgt,
  module Proarrow.Object
) where

import Proarrow.Core (CategoryOf(..), Obj, obj, src, tgt)

class Ob a => Ob' a
instance Ob a => Ob' a
type VacuusOb k = forall a. Ob' (a :: k)
