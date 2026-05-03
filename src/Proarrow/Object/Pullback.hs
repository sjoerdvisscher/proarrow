{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Pullback where

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, type (+->), lmap, UN)
import Proarrow.Object (pattern Objs)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD (..), Prod (..))
import Proarrow.Object.Initial (HasZeroObject (..))
import Proarrow.Profunctor.List (LIST (..), List (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))

-- | A cone is a bunch of arrows with a shared source.
data Cone (a :: PROD k) (bs :: LIST k) where
  Apex :: (Ob a) => Cone (PR a) (L '[])
  Leg :: a ~> b -> Cone (PR a) (L bs) -> Cone (PR a) (L (b : bs))

instance (CategoryOf k) => Profunctor (Cone :: LIST k +-> PROD k) where
  dimap l Nil Apex = Apex \\ l
  dimap (Prod l) (Cons r rs) (Leg f fs) = Leg (r . f . l) (dimap (Prod l) rs fs)
  r \\ Apex = r
  r \\ Leg l Apex = r \\ l
  r \\ Leg l c@(Leg _ c1) = r \\ l \\ c \\ c1

instance (HasProducts k) => MonoidalProfunctor (Cone :: LIST k +-> PROD k) where
  par0 = Apex
  Apex @a `par` rs = lmap (Prod (snd @_ @a)) rs \\ rs
  Leg l ls `par` (rs :: Cone r rs) = Leg (l . fst @_ @_ @(UN PR r)) (ls `par` rs) \\ l \\ rs

-- | A cosink (a.k.a a source) is a cone, but with the apex type hidden by an existential.
data Cosink (as :: [k]) where
  Cone :: Cone (PR a) (L as) -> Cosink as

-- | Pullbacks are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrows and the type, which we hide behind an existential.
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
