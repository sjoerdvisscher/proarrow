{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Profunctor.Exponential where

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (//), UN, type (+->))
import Proarrow.Category.Enriched.ThinCategory (ThinProfunctor (..), Discrete, withEq)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Object.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Profunctor.Product ((:*:) (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Category.Instance.Constraint ((:=>) (..), reifyExp, type (:-) (..))

data (p :~>: q) a b where
  Exp :: (Ob a, Ob b) => (forall c d. c ~> a -> b ~> d -> p c d -> q c d) -> (p :~>: q) a b

instance (Profunctor p, Profunctor q) => Profunctor (p :~>: q) where
  dimap l r (Exp f) = l // r // Exp \ca bd p -> f (l . ca) (bd . r) p
  r \\ Exp{} = r

instance (CategoryOf j, CategoryOf k) => Closed (PROD (j +-> k)) where
  type p ~~> q = PR (UN PR p :~>: UN PR q)
  withObExp r = r
  curry (Prod (Prof n)) = Prod (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q))
  apply = Prod (Prof \(Exp f :*: q) -> f id id q \\ q)
  Prod (Prof m) ^^^ Prod (Prof n) = Prod (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p)))

instance (ThinProfunctor p, ThinProfunctor q, Discrete j, Discrete k) => ThinProfunctor (p :~>: q :: j +-> k) where
  type HasArrow (p :~>: q) a b = (HasArrow p a b :=> HasArrow q a b)
  arr @a @b = Exp \ca bd p -> withEq ca (withEq bd (withArr p (unEntails (entails @(HasArrow p a b) @(HasArrow q a b)) arr)))
  withArr @a @b (Exp f) = reifyExp (Entails @(HasArrow p a b) @(HasArrow q a b) (withArr (f id id arr)))