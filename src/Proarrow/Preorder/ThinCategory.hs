module Proarrow.Preorder.ThinCategory where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Core (CategoryOf(..), UN, Is, obj, Promonad (..), Profunctor (..), CAT, type (+->))
import Proarrow.Preorder (CProfunctor (..), POS, cdimapDefault, CPromonad (..), PreorderOf(..), type (:-) (..), Dict (..))

type ThinProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p, Thin j, Thin k) => ThinProfunctor (p :: j +-> k) where
  type HasArrow (p :: j +-> k) (a :: k) (b :: j) :: Constraint
  type HasArrow p a b = ()
  arr :: (Ob a, Ob b, HasArrow p a b) => p a b
  withArr :: p a b -> (HasArrow p a b => r) -> r

class (ThinProfunctor ((~>) :: CAT k)) => Thin k
instance (ThinProfunctor ((~>) :: CAT k)) => Thin k

class HasArrow p a b => HasArrow' p a b
instance HasArrow p a b => HasArrow' p a b

type Codiscrete :: forall {j} {k}. j +-> k -> Constraint
class (ThinProfunctor p, forall c d. (Ob c, Ob d) => HasArrow' p c d) => Codiscrete (p :: j +-> k) where
  anyArr :: (Ob a, Ob b) => p a b
instance (ThinProfunctor p, forall c d. (Ob c, Ob d) => HasArrow' p c d) => Codiscrete (p :: j +-> k) where
  anyArr = arr

type Discrete :: forall {k}. k +-> k -> Constraint
class (ThinProfunctor p, forall c d. HasArrow p c d => c ~ d) => Discrete (p :: k +-> k) where
  withEq :: p a b -> (a ~ b => r) -> r
instance (ThinProfunctor p, forall c d. HasArrow p c d => c ~ d) => Discrete (p :: k +-> k) where
  withEq = withArr

newtype THIN k = T k
type instance UN T (T a) = a

class (Thin k, HasArrow (~>) (UN T a) (UN T b), COb a, COb b) => ThinCategory (a :: THIN k) b
instance (Thin k, HasArrow (~>) (UN T a) (UN T b), COb a, COb b) => ThinCategory (a :: THIN k) b

instance Thin k => CProfunctor (ThinCategory :: POS (THIN k)) where
  cdimap = cdimapDefault
  obs = Sub Dict
instance Thin k => CPromonad (ThinCategory :: POS (THIN k)) where
  cid @(T a) = Sub (withArr (obj @a) Dict)
  ccomp @a @b @c = Sub (withArr (arr @(~>) @(UN T b) @(UN T c) . arr @(~>) @(UN T a) @(UN T b)) Dict)

instance Thin k => PreorderOf (THIN k) where
  type (<=) = ThinCategory
  type COb a = (Is T a, Ob (UN T a))