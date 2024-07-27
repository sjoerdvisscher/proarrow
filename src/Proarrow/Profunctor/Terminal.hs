module Proarrow.Profunctor.Terminal (TerminalProfunctor (.., TerminalProfunctor')) where

import Proarrow.Category.Monoidal (Monoidal (par), MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..))
import Proarrow.Object (Obj, obj)

type TerminalProfunctor :: PRO j k
data TerminalProfunctor a b where
  TerminalProfunctor :: (Ob a, Ob b) => TerminalProfunctor a b

instance (CategoryOf j, CategoryOf k) => Profunctor (TerminalProfunctor :: PRO j k) where
  dimap l r TerminalProfunctor = TerminalProfunctor \\ l \\ r
  r \\ TerminalProfunctor = r

instance (Monoidal j, Monoidal k) => MonoidalProfunctor (TerminalProfunctor :: PRO j k) where
  lift0 = TerminalProfunctor
  lift2 (TerminalProfunctor' a1 b1) (TerminalProfunctor' a2 b2) = TerminalProfunctor' (a1 `par` a2) (b1 `par` b2)

getObs :: (CategoryOf j, CategoryOf k) => TerminalProfunctor (a :: j) (b :: k) -> (Obj a, Obj b)
getObs TerminalProfunctor = (obj, obj)

pattern TerminalProfunctor' :: (CategoryOf j, CategoryOf k) => Obj (a :: j) -> Obj (b :: k) -> TerminalProfunctor a b
pattern TerminalProfunctor' x y <- (getObs -> (x, y))
  where
    TerminalProfunctor' a b = TerminalProfunctor \\ a \\ b

{-# COMPLETE TerminalProfunctor' #-}
