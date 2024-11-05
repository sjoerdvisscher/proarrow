module Proarrow.Profunctor.Terminal (TerminalProfunctor (.., TerminalProfunctor)) where

import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..))
import Proarrow.Object (type Obj, pattern Obj)

type TerminalProfunctor :: PRO j k
data TerminalProfunctor a b where
  TerminalProfunctor' :: Obj a -> Obj b -> TerminalProfunctor (a :: j) (b :: k)

instance (CategoryOf j, CategoryOf k) => Profunctor (TerminalProfunctor :: PRO j k) where
  dimap l r TerminalProfunctor = TerminalProfunctor \\ l \\ r
  r \\ TerminalProfunctor = r

instance (Monoidal j, Monoidal k) => MonoidalProfunctor (TerminalProfunctor :: PRO j k) where
  par0 = TerminalProfunctor' par0 par0
  TerminalProfunctor' a1 b1 `par` TerminalProfunctor' a2 b2 = TerminalProfunctor' (a1 `par` a2) (b1 `par` b2)

pattern TerminalProfunctor :: (CategoryOf j, CategoryOf k) => (Ob (a :: j), Ob (b :: k)) => TerminalProfunctor a b
pattern TerminalProfunctor = TerminalProfunctor' Obj Obj

{-# COMPLETE TerminalProfunctor #-}
