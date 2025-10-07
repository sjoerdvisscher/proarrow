{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Adjunction where

import Data.Kind (Constraint)

import Proarrow.Category.Opposite (Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), rmap, (//), (:~>), type (+->))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepObj, trivialCorep)
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (CorepStar (..), RepCostar (..), Representable (..), repObj, trivialRep)
import Proarrow.Profunctor.Star (Star (..))
import Proarrow.Promonad (Procomonad (..))

-- | Adjunctions as heteromorphisms.
class (Representable p, Corepresentable p) => Adjunction p

instance (Representable p, Corepresentable p) => Adjunction p

leftAdjunct :: forall p a b. (Adjunction p, Ob a) => (p %% a ~> b) -> a ~> p % b
leftAdjunct = index . cotabulate @p

rightAdjunct :: forall p a b. (Adjunction p, Ob b) => a ~> p % b -> (p %% a ~> b)
rightAdjunct = coindex . tabulate @p

-- | The left adjoint of @((->) a)@ is @(,) a@.
instance Corepresentable (Star ((->) a)) where
  type Star ((->) a) %% b = (a, b)
  cotabulate f = Star \a b -> f (b, a)
  coindex (Star f) (a, b) = f b a
  corepMap f (a, b) = (a, f b)

-- | The right adjoint of @(,) a@ is @((->) a)@.
instance Representable (Costar ((,) a)) where
  type Costar ((,) a) % b = a -> b
  tabulate f = Costar \(a, b) -> f b a
  index (Costar g) a b = g (b, a)
  repMap f g = f . g

type Proadjunction :: forall {j} {k}. j +-> k -> k +-> j -> Constraint

-- | Adjunctions between two profunctors.
class (Profunctor p, Profunctor q) => Proadjunction (p :: j +-> k) (q :: k +-> j) where
  unit :: (Ob a) => (q :.: p) a a -- (~>) :~> q :.: p
  counit :: p :.: q :~> (~>)

instance (Representable f) => Proadjunction f (RepCostar f) where
  unit @a = RepCostar (repObj @f @a) :.: trivialRep
  counit (f :.: RepCostar g) = g . index f

instance (Corepresentable f) => Proadjunction (CorepStar f) f where
  unit @a = trivialCorep :.: CorepStar (corepObj @f @a)
  counit (CorepStar f :.: g) = coindex g . f

instance (Proadjunction l1 r1, Proadjunction l2 r2) => Proadjunction (l1 :.: l2) (r2 :.: r1) where
  unit :: forall a. (Ob a) => ((r2 :.: r1) :.: (l1 :.: l2)) a a
  unit = case unit @l2 @r2 @a of
    r2 :.: l2 ->
      l2 // case unit @l1 @r1 of
        r1 :.: l1 -> (r2 :.: r1) :.: (l1 :.: l2)
  counit ((l1 :.: l2) :.: (r2 :.: r1)) = counit (rmap (counit (l2 :.: r2)) l1 :.: r1)

instance (CategoryOf k) => Proadjunction (Id :: CAT k) Id where
  unit = Id id :.: Id id
  counit (Id f :.: Id g) = g . f

instance (Proadjunction q p) => Proadjunction (Op p) (Op q) where
  unit = case unit @q @p of q :.: p -> Op p :.: Op q
  counit (Op q :.: Op p) = Op (counit (p :.: q))

instance (Proadjunction p q) => Promonad (q :.: p) where
  id = unit
  (q :.: p) . (q' :.: p') = rmap (counit (p' :.: q)) q' :.: p

instance (Proadjunction p q) => Procomonad (p :.: q) where
  extract = counit
  duplicate (p :.: q) = p // case unit of q' :.: p' -> (p :.: q') :.: (p' :.: q)
