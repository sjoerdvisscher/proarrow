{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Preorder.ThinCategory where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, obj, type (+->))
import Proarrow.Preorder
  ( CProfunctor (..)
  , CPromonad (..)
  , Dict (..)
  , POS
  , PreorderOf (..)
  , cdimapDefault
  , type (:-) (..)
  )

type ThinProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p, Thin j, Thin k) => ThinProfunctor (p :: j +-> k) where
  type HasArrow (p :: j +-> k) (a :: k) (b :: j) :: Constraint
  type HasArrow p a b = ()
  arr :: (Ob a, Ob b, HasArrow p a b) => p a b
  withArr :: p a b -> ((HasArrow p a b) => r) -> r

class (ThinProfunctor ((~>) :: CAT k)) => Thin k
instance (ThinProfunctor ((~>) :: CAT k)) => Thin k

class (HasArrow p a b) => HasArrow' p a b
instance (HasArrow p a b) => HasArrow' p a b

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
  anyArr = arr

class (CodiscreteProfunctor ((~>) :: CAT k)) => Codiscrete k
instance (CodiscreteProfunctor ((~>) :: CAT k)) => Codiscrete k

class ((HasArrow p c d) ~ (c ~ d)) => ArrowIsId p c d where
  arrowIsIdProof :: HasArrow p c d => (c ~ d => r) -> r
instance ((HasArrow p c d) ~ (c ~ d)) => ArrowIsId p c d where
  arrowIsIdProof r = r

type DiscreteProfunctor :: forall {k}. k +-> k -> Constraint
class (ThinProfunctor p, forall c d. ArrowIsId p c d, Discrete k) => DiscreteProfunctor (p :: k +-> k) where
  withEq :: p a b -> ((a ~ b) => r) -> r
instance (ThinProfunctor p, forall c d. ArrowIsId p c d, Discrete k) => DiscreteProfunctor (p :: k +-> k) where
  withEq @a @b p r = withArr p (arrowIsIdProof @p @a @b r)

class (DiscreteProfunctor ((~>) :: CAT k)) => Discrete k
instance (DiscreteProfunctor ((~>) :: CAT k)) => Discrete k

newtype THIN k = T k
type instance UN T (T a) = a

class (Thin k, HasArrow (~>) (UN T a) (UN T b), COb a, COb b) => ThinCategory (a :: THIN k) b
instance (Thin k, HasArrow (~>) (UN T a) (UN T b), COb a, COb b) => ThinCategory (a :: THIN k) b

instance (Thin k) => CProfunctor (ThinCategory :: POS (THIN k)) where
  cdimap = cdimapDefault
  obs = Sub Dict
instance (Thin k) => CPromonad (ThinCategory :: POS (THIN k)) where
  cid @(T a) = Sub (withArr (obj @a) Dict)
  ccomp @a @b @c = Sub (withArr (arr @(~>) @(UN T b) @(UN T c) . arr @(~>) @(UN T a) @(UN T b)) Dict)

-- | A thin category as a preorder.
instance (Thin k) => PreorderOf (THIN k) where
  type (<=) = ThinCategory
  type COb a = (Is T a, Ob (UN T a))