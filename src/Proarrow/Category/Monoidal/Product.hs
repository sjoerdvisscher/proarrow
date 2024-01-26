{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Monoidal.Product where

import Proarrow.Category.Monoidal (Monoidal(..), SymMonoidal(..))
import Proarrow.Category.Instance.Product ((:**:)(..))

instance (Monoidal j, Monoidal k) => Monoidal (j, k) where
  type Unit = '(Unit, Unit)
  type '(a1, a2) ** '(b1, b2) = '(a1 ** b1, a2 ** b2)
  (f1 :**: f2) `par` (g1 :**: g2) = (f1 `par` g1) :**: (f2 `par` g2)
  leftUnitor (a1 :**: a2) = leftUnitor a1 :**: leftUnitor a2
  leftUnitorInv (a1 :**: a2) = leftUnitorInv a1 :**: leftUnitorInv a2
  rightUnitor (a1 :**: a2) = rightUnitor a1 :**: rightUnitor a2
  rightUnitorInv (a1 :**: a2) = rightUnitorInv a1 :**: rightUnitorInv a2
  associator (a1 :**: a2) (b1 :**: b2) (c1 :**: c2) = associator a1 b1 c1 :**: associator a2 b2 c2
  associatorInv (a1 :**: a2) (b1 :**: b2) (c1 :**: c2) = associatorInv a1 b1 c1 :**: associatorInv a2 b2 c2

instance (SymMonoidal j, SymMonoidal k) => SymMonoidal (j, k) where
  swap' (a1 :**: a2) (b1 :**: b2) = swap' a1 b1 :**: swap' a2 b2