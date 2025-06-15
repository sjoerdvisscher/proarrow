{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Cofree where

import Data.Kind (Constraint)
import Prelude (Int)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Forget (Forget (..))
import Proarrow.Profunctor.Representable (Representable (..), trivialRep)
import Proarrow.Profunctor.Star (Star (..))

type HasCofree :: forall {k}. (k -> Constraint) -> Constraint
class
  (CategoryOf k, Representable (Cofree ob), forall b. (Ob b) => ob (Cofree ob % b)) =>
  HasCofree (ob :: k -> Constraint)
  where
  type Cofree ob :: k +-> k
  lower' :: Cofree ob a b -> a ~> b
  section' :: (ob a) => a ~> b -> Cofree ob a b

lower :: forall ob a. (HasCofree ob, Ob a) => Cofree ob % a ~> a
lower = lower' @ob trivialRep

section :: forall ob a. (HasCofree ob, ob a, Ob a) => a ~> Cofree ob % a
section = index @(Cofree ob) (section' @ob id)

type CofreeSub :: forall (ob :: OB k) -> k +-> SUBCAT ob
data CofreeSub ob a b where
  CofreeSub :: (ob a) => a ~> b -> CofreeSub ob (SUB a) b

instance (CategoryOf k) => Profunctor (CofreeSub (ob :: OB k)) where
  dimap (Sub f) g (CofreeSub h) = CofreeSub (g . h . f)
  r \\ CofreeSub p = r \\ p

instance (HasCofree ob) => Representable (CofreeSub ob) where
  type CofreeSub ob % a = SUB (Cofree ob % a)
  index (CofreeSub f) = Sub (index (section' @ob f)) \\ f
  tabulate (Sub f) = CofreeSub (lower' @ob (tabulate f))
  repMap f = Sub (repMap @(Cofree ob) f) \\ f

instance (HasCofree ob) => Adjunction (Forget ob) (CofreeSub ob) where
  unit = CofreeSub id :.: Forget id
  counit (Forget f :.: CofreeSub g) = g . f

class Test a where
  test :: a -> Int
instance HasCofree Test where
  type Cofree Test = Star ((,) Int)
  lower' (Star f) a = case f a of (_, b) -> b
  section' f = Star \a -> (test a, f a)
instance Test (Int, a) where
  test (i, _) = i