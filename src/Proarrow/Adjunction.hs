{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant map" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Adjunction where

import Proarrow.Core (CAT, PRO, Profunctor(..), Promonad (..), CategoryOf(..), (:~>), (//), rmap)
import Proarrow.Functor (Functor(..))
import Data.Kind (Constraint)
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Profunctor.Identity (Id(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Profunctor.Costar (Costar(..))

type Adjunction :: forall {j} {k}. PRO k j -> PRO j k -> Constraint
class (Profunctor p, Profunctor q) => Adjunction (p :: PRO k j) (q :: PRO j k) where
  unit :: Ob a => (q :.: p) a a -- (~>) :~> q :.: p
  counit :: p :.: q :~> (~>)

leftAdjunct
  :: forall l r a b. (Adjunction (Star l) (Star r), Functor r)
  => Ob a => (l a ~> b) -> (a ~> r b)
leftAdjunct f = case unit @(Star l) @(Star r) @a of Star r :.: Star l -> map (f . l) . r

rightAdjunct
  :: forall l r a b. (Adjunction (Star l) (Star r), Functor l)
  => Ob b => (a ~> r b) -> (l a ~> b)
rightAdjunct f = counit (Star (map id) :.: Star f) \\ f

unitFromStarUnit
  :: forall l r a. (Functor l, Ob a) => (a ~> r (l a)) -> (Star r :.: Star l) a a
unitFromStarUnit f = Star f :.: Star id

counitFromStarCounit
  :: Functor l => (forall c. Ob c => l (r c) ~> c) -> (Star l :.: Star r) a b -> (a ~> b)
counitFromStarCounit f (Star l :.: Star r) = f . map r . l

instance Functor f => Adjunction (Star f) (Costar f) where
  unit = Costar (map id) :.: Star (map id)
  counit (Star f :.: Costar g) = g . f

instance (Functor f, Functor g, Adjunction (Star f) (Star g)) => Adjunction (Costar f) (Costar g) where
  unit :: forall a. (Ob a) => (Costar g :.: Costar f) a a
  unit = Costar id :.: Costar (counit (Star (map id) :.: Star id))
  counit :: forall a b. (Costar f :.: Costar g) a b -> a ~> b
  counit (Costar f :.: Costar g) = case unit @(Star f) @(Star g) @a of Star g' :.: Star f' -> g . map (f . f') . g'

instance (Adjunction l1 r1, Adjunction l2 r2) => Adjunction (l1 :.: l2) (r2 :.: r1) where
  unit :: forall a. Ob a => ((r2 :.: r1) :.: (l1 :.: l2)) a a
  unit = case unit @l2 @r2 @a of
    r2 :.: l2 -> l2 // case unit @l1 @r1 of
      r1 :.: l1 -> (r2 :.: r1) :.: (l1 :.: l2)
  counit ((l1 :.: l2) :.: (r2 :.: r1)) = counit (rmap (counit (l2 :.: r2)) l1 :.: r1)

instance Adjunction (Star ((,) a)) (Star ((->) a)) where
  unit = unitFromStarUnit \a b -> (b, a)
  counit = counitFromStarCounit \(a, f) -> f a

instance CategoryOf k => Adjunction (Id :: CAT k) Id where
  unit = Id id :.: Id id
  counit (Id f :.: Id g) = g . f

instance Adjunction p q => Promonad (q :.: p) where
  id = unit
  (q :.: p) . (q' :.: p')= rmap (counit (p' :.: q)) q' :.: p

