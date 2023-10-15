module Proarrow.Profunctor.Terminal (TerminalProfunctor(.., TerminalProfunctor')) where

import Proarrow.Core (PRO, Profunctor (..), CategoryOf, Category (..))
import Proarrow.Object (Obj, obj)

type TerminalProfunctor :: PRO j k
data TerminalProfunctor a b where
  TerminalProfunctor :: (Ob a, Ob b) => TerminalProfunctor a b

instance (CategoryOf j, CategoryOf k) => Profunctor (TerminalProfunctor :: PRO j k) where
  dimap l r TerminalProfunctor = TerminalProfunctor \\ l \\ r
  r \\ TerminalProfunctor = r


getObs :: (CategoryOf j, CategoryOf k) => TerminalProfunctor (a :: j) (b :: k) -> (Obj a, Obj b)
getObs TerminalProfunctor = (obj, obj)

pattern TerminalProfunctor' :: (CategoryOf j, CategoryOf k) => Obj (a :: j) -> Obj (b :: k) -> TerminalProfunctor a b
pattern TerminalProfunctor' x y <- (getObs -> (x, y)) where
  TerminalProfunctor' a b = TerminalProfunctor \\ a \\ b

{-# COMPLETE TerminalProfunctor' #-}