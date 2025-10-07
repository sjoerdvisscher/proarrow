{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Cofree where

import Data.Kind (Constraint)
import Prelude (Int)

import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), trivialRep)
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

data family CofreeSub :: forall (ob :: OB k) -> k +-> SUBCAT ob
instance (HasCofree ob) => FunctorForRep (CofreeSub ob) where
  type CofreeSub ob @ a = SUB (Cofree ob % a)
  fmap f = Sub (repMap @(Cofree ob) f) \\ f
instance (HasCofree ob) => Corepresentable (Rep (CofreeSub (ob :: OB k))) where
  type Rep (CofreeSub ob) %% a = UN SUB a
  coindex (Rep (Sub f)) = lower @ob . f
  cotabulate f = Rep (Sub (repMap @(Cofree ob) f . section @ob)) \\ f
  corepMap (Sub f) = f

class Test a where
  test :: a -> Int
instance HasCofree Test where
  type Cofree Test = Star ((,) Int)
  lower' (Star f) a = case f a of (_, b) -> b
  section' f = Star \a -> (test a, f a)
instance Test (Int, a) where
  test (i, _) = i