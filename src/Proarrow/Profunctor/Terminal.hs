module Proarrow.Profunctor.Terminal where

import Proarrow.Core (PRO, Profunctor (..), CategoryOf, Category (..))

type TerminalProfunctor :: PRO j k
data TerminalProfunctor a b where
  TerminalProfunctor :: (Ob a, Ob b) => TerminalProfunctor a b

instance (CategoryOf j, CategoryOf k) => Profunctor (TerminalProfunctor :: PRO j k) where
  dimap l r TerminalProfunctor = TerminalProfunctor \\ l \\ r
  r \\ TerminalProfunctor = r
