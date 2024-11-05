{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Adjunction where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), isObPar)
import Proarrow.Core (CAT, CategoryOf (..), Obj, PRO, Profunctor (..), Promonad (..), rmap, (//), (:~>), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (RepCostar (..), Representable (..), repObj)
import Proarrow.Profunctor.Star (Star (..))
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Category.Opposite (Op (..))

type Adjunction :: forall {j} {k}. PRO k j -> PRO j k -> Constraint

-- | Adjunctions between two profunctors.
class (Profunctor p, Profunctor q) => Adjunction (p :: PRO k j) (q :: PRO j k) where
  unit :: (Ob a) => (q :.: p) a a -- (~>) :~> q :.: p
  counit :: p :.: q :~> (~>)

unit' :: forall p q a b. (Adjunction p q) => a ~> b -> (q :.: p) a b
unit' f = rmap f (unit @p @q @a) \\ f

leftAdjunct
  :: forall l r a b
   . (Adjunction l r, Representable l, Representable r, Ob a)
  => (l % a ~> b)
  -> r a b
leftAdjunct f = case unit @l @r of r :.: l -> rmap (f . index l) r

rightAdjunct
  :: forall l r a b
   . (Adjunction l r, Representable l, Representable r, Ob b)
  => r a b
  -> (l % a ~> b)
rightAdjunct f = counit (tabulate @l (repMap @l @a id) :.: f) \\ f

unitFromRepUnit
  :: forall l r a. (Representable l, Representable r, Ob a) => (a ~> r % (l % a)) -> (r :.: l) a a
unitFromRepUnit f = tabulate f :.: tabulate id \\ repObj @l @a

counitFromRepCounit
  :: forall l r. (Representable l, Representable r) => (forall c. (Ob c) => l % (r % c) ~> c) -> (l :.: r) :~> (~>)
counitFromRepCounit f (l :.: r) = f . repMap @l (index r) . index l \\ r

instance (Functor f) => Adjunction (Star f) (Costar f) where
  unit = Costar (map id) :.: Star (map id)
  counit (Star f :.: Costar g) = g . f

instance (Representable f) => Adjunction f (RepCostar f) where
  unit @a = let fa = repMap @f @a id in RepCostar fa :.: tabulate fa
  counit (f :.: RepCostar g) = g . index f

instance (Functor f, Functor g, Adjunction (Star f) (Star g)) => Adjunction (Costar f) (Costar g) where
  unit :: forall a. (Ob a) => (Costar g :.: Costar f) a a
  unit = Costar id :.: Costar (counit (Star (map id) :.: Star id))
  counit :: forall a b. (Costar f :.: Costar g) a b -> a ~> b
  counit (Costar f :.: Costar g) = case unit @(Star f) @(Star g) @a of Star g' :.: Star f' -> g . map (f . f') . g'

instance (Adjunction l1 r1, Adjunction l2 r2) => Adjunction (l1 :.: l2) (r2 :.: r1) where
  unit :: forall a. (Ob a) => ((r2 :.: r1) :.: (l1 :.: l2)) a a
  unit = case unit @l2 @r2 @a of
    r2 :.: l2 ->
      l2 // case unit @l1 @r1 of
        r1 :.: l1 -> (r2 :.: r1) :.: (l1 :.: l2)
  counit ((l1 :.: l2) :.: (r2 :.: r1)) = counit (rmap (counit (l2 :.: r2)) l1 :.: r1)

instance Adjunction (Star ((,) a)) (Star ((->) a)) where
  unit = unitFromRepUnit \a b -> (b, a)
  counit = counitFromRepCounit \(a, f) -> f a

instance (CategoryOf k) => Adjunction (Id :: CAT k) Id where
  unit = Id id :.: Id id
  counit (Id f :.: Id g) = g . f

instance Adjunction q p => Adjunction (Op p) (Op q) where
  unit = case unit @q @p of q :.: p -> Op p :.: Op q
  counit (Op q :.: Op p) = Op (counit (p :.: q))

instance (Adjunction p q) => Promonad (q :.: p) where
  id = unit
  (q :.: p) . (q' :.: p') = rmap (counit (p' :.: q)) q' :.: p

instance (Adjunction p q) => Procomonad (p :.: q) where
  extract = counit
  duplicate (p :.: q) = p // case unit of q' :.: p' -> (p :.: q') :.: (p' :.: q)

instance
  (MonoidalProfunctor r, Adjunction l r, Representable l, Representable r, Monoidal j, Monoidal k)
  => MonoidalProfunctor (RepCostar l :: j +-> k)
  where
  par0 = RepCostar (counit @l @r (tabulate (repMap @l @Unit id) :.: par0)) \\ (par0 :: Obj (Unit :: k))
  RepCostar @x1 fx `par` RepCostar @y1 fy =
    (fx `par` fy) // isObPar @x1 @y1 $
      RepCostar (rightAdjunct @l @r (leftAdjunct @l @r @x1 fx `par` leftAdjunct @l @r @y1 fy))
