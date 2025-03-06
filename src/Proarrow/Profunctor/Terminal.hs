module Proarrow.Profunctor.Terminal (TerminalProfunctor (.., TerminalProfunctor)) where

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), type (+->), Promonad (..))
import Proarrow.Object (pattern Obj, type Obj)
import Proarrow.Preorder.ThinCategory (Codiscrete, ThinProfunctor (..))

type TerminalProfunctor :: j +-> k
data TerminalProfunctor a b where
  TerminalProfunctor' :: Obj a -> Obj b -> TerminalProfunctor (a :: j) (b :: k)

instance (CategoryOf j, CategoryOf k) => Profunctor (TerminalProfunctor :: j +-> k) where
  dimap l r TerminalProfunctor = TerminalProfunctor \\ l \\ r
  r \\ TerminalProfunctor = r

instance (CategoryOf k) => Promonad (TerminalProfunctor :: k +-> k) where
  id = TerminalProfunctor
  TerminalProfunctor . TerminalProfunctor = TerminalProfunctor

instance (Monoidal j, Monoidal k) => MonoidalProfunctor (TerminalProfunctor :: j +-> k) where
  par0 = TerminalProfunctor' par0 par0
  TerminalProfunctor' a1 b1 `par` TerminalProfunctor' a2 b2 = TerminalProfunctor' (a1 `par` a2) (b1 `par` b2)

instance (CategoryOf k) => DaggerProfunctor (TerminalProfunctor :: k +-> k) where
  dagger TerminalProfunctor = TerminalProfunctor

pattern TerminalProfunctor :: forall {j} {k} a b. (CategoryOf j, CategoryOf k) => (Ob (a :: j), Ob (b :: k)) => TerminalProfunctor a b
pattern TerminalProfunctor = TerminalProfunctor' Obj Obj

{-# COMPLETE TerminalProfunctor #-}

instance (CategoryOf j, CategoryOf k) => ThinProfunctor (TerminalProfunctor :: j +-> k) where
  arr = TerminalProfunctor
  withArr TerminalProfunctor r = r

instance (CategoryOf j, CategoryOf k) => Codiscrete (TerminalProfunctor :: j +-> k)