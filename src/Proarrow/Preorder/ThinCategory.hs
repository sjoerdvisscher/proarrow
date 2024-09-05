module Proarrow.Preorder.ThinCategory where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf(..), UN, Is, obj, Promonad (..))
import Proarrow.Preorder (CProfunctor (..), POS, cdimapDefault, CPromonad (..), PreorderOf(..), type (:-) (..), Dict (..))

class CategoryOf k => Thin k where
  type HasArrow (a :: k) (b :: k) :: Constraint
  arr :: (Ob (a :: k), Ob b, HasArrow a b) => a ~> b
  withArr :: ((a :: k) ~> b) -> (HasArrow a b => r) -> r

newtype THIN k = T k
type instance UN T (T a) = a

class (Thin k, HasArrow (UN T a) (UN T b), COb a, COb b) => ThinCategory (a :: THIN k) b
instance (Thin k, HasArrow (UN T a) (UN T b), COb a, COb b) => ThinCategory (a :: THIN k) b

instance Thin k => CProfunctor (ThinCategory :: POS (THIN k)) where
  cdimap = cdimapDefault
  obs = Sub Dict
instance Thin k => CPromonad (ThinCategory :: POS (THIN k)) where
  cid @(T a) = Sub (withArr (obj @a) Dict)
  ccomp @a @b @c = Sub (withArr (arr @k @(UN T b) @(UN T c) . arr @k @(UN T a) @(UN T b)) Dict)

instance Thin k => PreorderOf (THIN k) where
  type (<=) = ThinCategory
  type COb a = (Is T a, Ob (UN T a))