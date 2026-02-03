module Proarrow.Profunctor.Constant where

import Proarrow.Core (CategoryOf (..), Promonad (..), type (+->), Optic)
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Profunctor.Representable (rep, Rep)
import Proarrow.Profunctor.Corepresentable (corep, Corep)

data family Constant :: k -> j +-> k
instance (CategoryOf j, CategoryOf k, Ob c) => FunctorForRep (Constant c :: j +-> k) where
  type Constant c @ a = c
  fmap _ = id

view :: forall {k} {c} (s :: k) (t :: k) a b. (CategoryOf k, Ob a, Ob b, c (Rep (Constant a))) => Optic c s t a b -> s ~> a
view l = rep @(Constant a) l id

review :: forall {k} {c} (s :: k) (t :: k) a b. (CategoryOf k, Ob a, Ob b, c (Corep (Constant b))) => Optic c s t a b -> b ~> t
review l = corep @(Constant b) l id