module Proarrow.Profunctor.Constant where

import Proarrow.Core (CategoryOf (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Optic (Optic', Optic_(..))
import Proarrow.Profunctor.Corepresentable (Corep (..), corep)
import Proarrow.Profunctor.Representable (Rep (..), rep)

data family Constant :: k -> j +-> k
instance (CategoryOf j, CategoryOf k, Ob c) => FunctorForRep (Constant c :: j +-> k) where
  type Constant c @ a = c
  fmap _ = id

view :: forall {k} c (s :: k) a. (CategoryOf k, Ob a => c (Rep (Constant a))) => Optic' c s a -> s ~> a
view (Optic l) = over (rep @(Constant a)) l id

infixl 8 ^.
(^.) :: (c (Rep (Constant a))) => s -> Optic' c s a -> a
(^.) s l = view l s

review :: forall {k} c (t :: k) b. (CategoryOf k, Ob b => c (Corep (Constant b))) => Optic' c t b -> b ~> t
review (Optic l) = over (corep @(Constant b)) l id

infixr 8 #
(#) :: forall {k} c (t :: k) b. (CategoryOf k, c (Corep (Constant b))) => Optic' c t b -> b ~> t
(#) = review
