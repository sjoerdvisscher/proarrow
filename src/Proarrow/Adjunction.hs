{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant map" #-}
module Proarrow.Adjunction where

import Proarrow.Core (CAT, PRO, Profunctor(..), Category (..), CategoryOf, (:~>), type (~>), (//))
import Proarrow.Functor (Functor(..), withFCod')
import Data.Kind (Constraint)
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Profunctor.Identity (Id(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Profunctor.Costar (Costar(..))

type Adjunction :: forall {j} {k}. PRO k j -> PRO j k -> Constraint
class (Profunctor p, Profunctor q) => Adjunction (p :: PRO k j) (q :: PRO j k) where
  unit :: Ob a => (p :.: q) a a -- (~>) :~> p :.: q
  counit :: q :.: p :~> (~>)

leftAdjunct
  :: forall l r a b. (Adjunction (Star l) (Star r), Functor r)
  => Ob a => (l a ~> b) -> (a ~> r b)
leftAdjunct f = case unit @(Star l) @(Star r) @a of Star l :.: Star r -> map (f . l) . r

rightAdjunct
  :: forall l r a b. (Adjunction (Star l) (Star r), Functor l)
  => Ob b => (a ~> r b) -> (l a ~> b)
rightAdjunct f = counit (Star f :.: Star (map id)) \\ f

unitFromStarUnit
  :: forall l r a. (Functor l, Ob a) => (a ~> r (l a)) -> (Star l :.: Star r) a a
unitFromStarUnit f = withFCod' @l @a \la -> Star la :.: Star f

counitFromStarCounit
  :: Functor l => (forall c. Ob c => l (r c) ~> c) -> (Star r :.: Star l) a b -> (a ~> b)
counitFromStarCounit f (Star r :.: Star l) = f . map r . l

instance Functor f => Adjunction (Star f) (Costar f) where
  unit = Star (map id) :.: Costar (map id)
  counit (Costar f :.: Star g) = f . g

instance (Functor f, Functor g, Adjunction (Star f) (Star g)) => Adjunction (Costar f) (Costar g) where
  unit :: forall a. (Ob a) => (Costar f :.: Costar g) a a
  unit = withFCod' @g @a \ga -> Costar (counit (Star ga :.: Star (map id))) :.: Costar id
  counit :: forall a b. (Costar g :.: Costar f) a b -> a ~> b
  counit (Costar g :.: Costar f) = case unit @(Star f) @(Star g) @a of Star f' :.: Star g' -> g . map (f . f') . g'

instance (Adjunction l1 r1, Adjunction l2 r2) => Adjunction (l2 :.: l1) (r1 :.: r2) where
  unit :: forall a. Ob a => ((l2 :.: l1) :.: (r1 :.: r2)) a a
  unit = case unit @l2 @r2 @a of
    l2 :.: r2 -> l2 // case unit @l1 @r1 of
      l1 :.: r1 -> (l2 :.: l1) :.: (r1 :.: r2)
  counit ((r1 :.: r2) :.: (l2 :.: l1)) = counit (r1 :.: l1) . counit (r2 :.: l2)

instance Adjunction (Star ((,) a)) (Star ((->) a)) where
  unit = unitFromStarUnit \a b -> (b, a)
  counit = counitFromStarCounit \(a, f) -> f a

instance CategoryOf k => Adjunction (Id :: CAT k) Id where
  unit = Id id :.: Id id
  counit (Id f :.: Id g) = f . g
