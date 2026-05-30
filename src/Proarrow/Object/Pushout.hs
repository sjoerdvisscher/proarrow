{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Object.Pushout where

import Prelude (($))

import Proarrow.Category.Opposite (OPPOSITE, Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, type (+->), rmap, UN, (//))
import Proarrow.Object (pattern Objs)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts, COPROD (..), Coprod (..))
import Proarrow.Object.Initial (HasZeroObject (..))
import Proarrow.Object.Pullback (Cone (..), Cosink (..), HasPullbacks (..))
import Proarrow.Profunctor.List (LIST (..), List (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Profunctor.Identity (Id(..))

-- | A cocone is a bunch of arrows with a shared target.
data Cocone (bs :: LIST k) (a :: COPROD k) where
  Coapex :: (Ob a) => Cocone (L '[]) (COPR a)
  Coleg :: b ~> a -> Cocone (L bs) (COPR a) -> Cocone (L (b : bs)) (COPR a)

instance (CategoryOf k) => Profunctor (Cocone :: COPROD k +-> LIST k) where
  dimap Nil r Coapex = Coapex \\ r
  dimap (Cons l ls) r@(Coprod (Id r')) (Coleg f fs) = Coleg (r' . f . l) (dimap ls r fs)
  r \\ Coapex = r
  r \\ Coleg l Coapex = r \\ l
  r \\ Coleg l c@(Coleg _ c1) = r \\ l \\ c \\ c1

instance (HasCoproducts k) => MonoidalProfunctor (Cocone :: COPROD k +-> LIST k) where
  par0 = Coapex
  Coapex @l `par` rs = rmap (Coprod (Id (rgt @_ @l))) rs \\ rs
  Coleg l ls `par` (rs :: Cocone rs r) = Coleg (lft @_ @_ @(UN COPR r)  . l) (ls `par` rs) \\ l \\ rs

-- | A sink is a cocone, but with the apex type hidden by an existential.
data Sink (as :: [k]) where
  Cocone :: Cocone (L as) (COPR a) -> Sink as

-- | Pushouts are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrows and the type, which we hide behind an existential.
class (HasCoproducts k) => HasPushouts k where
  pushout :: forall (o :: k) a b. o ~> a -> o ~> b -> Sink [a, b]

-- | In a thin category, arrows don't carry information, so pushouts are just coproducts.
thinPushout :: forall {k} (o :: k) a b. HasCoproducts k => o ~> a -> o ~> b -> Sink [a, b]
thinPushout l r = l // r // withObCoprod @k @a @b $ Cocone $ Coleg (lft @k @a @b) $ Coleg (rgt @k @a @b) Coapex

coequalizer :: forall {k} (a :: k) b. (HasPushouts k) => a ~> b -> a ~> b -> Sink '[b]
coequalizer f@Objs g = case pushout (obj @b ||| f) (obj @b ||| g) of
  Cocone (Coleg _ cocone) -> Cocone cocone

cokernel :: (HasPushouts k, HasZeroObject k) => (a :: k) ~> b -> Sink '[b]
cokernel f@Objs = coequalizer zero f

instance (HasPullbacks k) => HasPushouts (OPPOSITE k) where
  pushout (Op l) (Op r) = case pullback l r of Cone (Leg f (Leg g Apex)) -> Cocone (Coleg (Op f) (Coleg (Op g) Coapex))

instance (HasPushouts k) => HasPullbacks (OPPOSITE k) where
  pullback (Op l) (Op r) = case pushout l r of Cocone (Coleg f (Coleg g Coapex)) -> Cone (Leg (Op f) (Leg (Op g) Apex))
