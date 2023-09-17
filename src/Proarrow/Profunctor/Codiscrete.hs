{-# LANGUAGE UndecidableInstances #-}
module Proarrow.Profunctor.Codiscrete where

import Proarrow.Core (PRO, CategoryOf, Category(..), Profunctor(..))
import Proarrow.Object (Obj)

type Codiscrete :: PRO i j
data Codiscrete a b where
  Codiscrete :: Obj a -> Obj b -> Codiscrete a b
instance (CategoryOf i, CategoryOf j) => Profunctor (Codiscrete :: PRO i j) where
  dimap l r Codiscrete{} = Codiscrete id id \\ l \\ r
  r \\ Codiscrete a b = r \\ a \\ b
