module Proarrow.Profunctor.Exponential where

import Proarrow.Core (Profunctor(..), CategoryOf(..), Promonad(..), (//))

data (p :~>: q) a b where
  Exp :: (Ob a, Ob b) => (forall c d. c ~> a -> b ~> d -> p c d -> q c d) -> (p :~>: q) a b

instance (Profunctor p, Profunctor q) => Profunctor (p :~>: q) where
  dimap l r (Exp f) = l // r // Exp \ca bd p -> f (l . ca) (bd . r) p
  r \\ Exp{} = r
