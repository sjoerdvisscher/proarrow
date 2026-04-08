module Proarrow.Profunctor.Constant where

import Proarrow.Core (CategoryOf (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Profunctor.Corepresentable (Corep, corep)
import Proarrow.Profunctor.Representable (Rep (..), rep)

data family Constant :: k -> j +-> k
instance (CategoryOf j, CategoryOf k, Ob c) => FunctorForRep (Constant c :: j +-> k) where
  type Constant c @ a = c
  fmap _ = id

type Getting r s a = Rep (Constant r) a a -> Rep (Constant r) s s

view :: forall {k} (s :: k) a. (CategoryOf k, Ob a) => Getting a s a -> s ~> a
view l = rep @(Constant a) l id

infixl 8 ^.
(^.) :: s -> Getting a s a -> a
(^.) s l = view l s

type AReview r s a = Corep (Constant r) a a -> Corep (Constant r) s s

review :: forall {k} (t :: k) b. (CategoryOf k, Ob b) => AReview b t b -> b ~> t
review l = corep @(Constant b) l id

infixr 8 #
(#) :: forall {k} (t :: k) b. (CategoryOf k, Ob b) => AReview b t b -> b ~> t
(#) = review
