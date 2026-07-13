{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Enriched.Thin where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Instance.Zero (Bottom (..), Zero)
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), type (+->))

type ThinProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => ThinProfunctor (p :: j +-> k) where
  type HasArrow (p :: j +-> k) (a :: k) (b :: j) :: Constraint
  type HasArrow p a b = ()
  arr :: (Ob a, Ob b, HasArrow p a b) => p a b
  withArr :: p a b -> ((HasArrow p a b, Ob a, Ob b) => r) -> r

instance ThinProfunctor Zero where
  arr = no
  withArr = \case {}

class (HasArrow (Hom k) a a) => HasIdArrow k a
instance (HasArrow (Hom k) a a) => HasIdArrow k a

class (ThinProfunctor (Hom k), CategoryOf k, forall a. (Ob a) => HasIdArrow k a) => Thin k
instance (ThinProfunctor (Hom k), CategoryOf k, forall a. (Ob a) => HasIdArrow k a) => Thin k

class (ThinProfunctor p, Ob a, Ob b, HasArrow p a b) => HasArrow' p a b where arr' :: p a b
instance (ThinProfunctor p, Ob a, Ob b, HasArrow p a b) => HasArrow' p a b where arr' = arr

type CodiscreteProfunctor :: forall {j} {k}. j +-> k -> Constraint
class
  (ThinProfunctor p, forall c d. (Ob c, Ob d) => HasArrow' p c d, Codiscrete j, Codiscrete k) =>
  CodiscreteProfunctor (p :: j +-> k)
  where
  anyArr :: (Ob a, Ob b) => p a b
instance
  (ThinProfunctor p, forall c d. (Ob c, Ob d) => HasArrow' p c d, Codiscrete j, Codiscrete k)
  => CodiscreteProfunctor (p :: j +-> k)
  where
  anyArr = arr'

type Codiscrete k = CodiscreteProfunctor (Hom k)

class ((c) => d, (d) => c) => c <=> d
instance ((c) => d, (d) => c) => c <=> d

class ((HasArrow p a b) => Bottom) => HasNoArrow p a b where
  arrowIsBottomProof :: (HasArrow p a b) => r
instance ((HasArrow p a b) => Bottom) => HasNoArrow p a b where
  arrowIsBottomProof = no

type DiscreteProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (ThinProfunctor p, forall a b. (Ob a, Ob b) => HasNoArrow p a b) => DiscreteProfunctor (p :: j +-> k) where
  exfalso :: p a b -> r
instance (ThinProfunctor p, forall a b. (Ob a, Ob b) => HasNoArrow p a b) => DiscreteProfunctor (p :: j +-> k) where
  exfalso @a @b p = withArr p (arrowIsBottomProof @p @a @b)

class ((HasArrow (Hom k) c d) <=> (c ~ d)) => ArrowIsId k c d where
  arrowIsIdProof :: (HasArrow (Hom k) c d) => ((c ~ d) => r) -> r
instance ((HasArrow (Hom k) c d) <=> (c ~ d)) => ArrowIsId k c d where
  arrowIsIdProof r = r

-- | Note: @Discrete k@ is not the same as @DiscreteProfunctor (Hom k)@!
class (Thin k, forall c d. (Ob c, Ob d) => ArrowIsId k c d) => Discrete k where
  withEq :: (a :: k) ~> b -> ((a ~ b) => r) -> r

instance (Thin k, forall c d. (Ob c, Ob d) => ArrowIsId k c d) => Discrete k where
  withEq @a @b f r = withArr f (arrowIsIdProof @k @a @b r)
