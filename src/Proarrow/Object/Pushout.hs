{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Object.Pushout where

import Proarrow.Category.Opposite (OPPOSITE, Op (..))
import Proarrow.Core (CategoryOf (..), obj)
import Proarrow.Object (pattern Objs)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Object.Initial (HasZeroObject (..))
import Proarrow.Object.Pullback (Cone (..), Cosink (..), HasPullbacks (..))

data Cocone (bs :: [k]) (a :: k) where
  Coapex :: (Ob a) => Cocone '[] a
  Coleg :: b ~> a -> Cocone bs a -> Cocone (b : bs) a
data Sink (as :: [k]) where
  Cocone :: Cocone as a -> Sink as

-- | Composition of spans needs a pushout, an inherently dependently typed concept.
-- So we can't express it properly in Haskell, but the injection arrows can still do the right thing.
class (HasCoproducts k) => HasPushouts k where
  pushout :: forall (o :: k) a b. o ~> a -> o ~> b -> Sink [a, b]

coequalizer :: forall {k} (a :: k) b. (HasPushouts k) => a ~> b -> a ~> b -> Sink '[b]
coequalizer f@Objs g = case pushout (obj @b ||| f) (obj @b ||| g) of
  Cocone (Coleg _ cocone) -> Cocone cocone

cokernel :: (HasPushouts k, HasZeroObject k) => (a :: k) ~> b -> Sink '[b]
cokernel f@Objs = coequalizer zero f

instance (HasPullbacks k) => HasPushouts (OPPOSITE k) where
  pushout (Op l) (Op r) = case pullback l r of Cone (Leg f (Leg g Apex)) -> Cocone (Coleg (Op f) (Coleg (Op g) Coapex))

instance (HasPushouts k) => HasPullbacks (OPPOSITE k) where
  pullback (Op l) (Op r) = case pushout l r of Cocone (Coleg f (Coleg g Coapex)) -> Cone (Leg (Op f) (Leg (Op g) Apex))
