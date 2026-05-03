{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Pullback where

import Proarrow.Core (CategoryOf (..), obj)
import Proarrow.Object (pattern Objs)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts)
import Proarrow.Object.Initial (HasZeroObject (..))

data Cone (a :: k) (bs :: [k]) where
  Apex :: (Ob a) => Cone a '[]
  Leg :: a ~> b -> Cone a bs -> Cone a (b : bs)
data Cosink (as :: [k]) where
  Cone :: Cone a as -> Cosink as

-- | Composition of spans needs a pullback, an inherently dependently typed concept.
-- So we can't express it properly in Haskell, but the projection arrows can still do the right thing.
class (HasProducts k) => HasPullbacks k where
  pullback :: forall (o :: k) a b. a ~> o -> b ~> o -> Cosink [a, b]

equalizer :: forall {k} (a :: k) b. (HasPullbacks k) => a ~> b -> a ~> b -> Cosink '[a]
equalizer f@Objs g = case pullback (obj @a &&& f) (obj @a &&& g) of
  Cone (Leg _ cone) -> Cone cone

kernel :: (HasPullbacks k, HasZeroObject k) => (a :: k) ~> b -> Cosink '[a]
kernel f@Objs = equalizer zero f

class ik `InternalIn` k where
  type C0 ik :: k
  type C1 ik :: k
  source :: C1 ik ~> (C0 ik :: k)
  target :: C1 ik ~> (C0 ik :: k)
  identity :: C0 ik ~> (C1 ik :: k)
  compose :: Cosink [C1 ik, C1 ik, C1 ik :: k] -- first arrow projection, second arrow projection, composite
