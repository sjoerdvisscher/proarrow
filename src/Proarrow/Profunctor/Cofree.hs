{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Cofree where

import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction (..), counitFromRepCounit, unitFromRepUnit)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Forget (Forget)
import Proarrow.Profunctor.Representable (Representable (..), dimapRep, repObj)

type HasCofree :: forall {k}. (k -> Constraint) -> Constraint
class
  (CategoryOf k, Representable (Cofree ob), forall b. (Ob b) => ob (Cofree ob % b)) =>
  HasCofree (ob :: k -> Constraint)
  where
  type Cofree ob :: k +-> k
  lower' :: Cofree ob a b -> a ~> b
  section' :: (ob b) => a ~> b -> Cofree ob a b

lower :: forall ob a. (HasCofree ob, Ob a) => Cofree ob % a ~> a
lower = lower' @ob (tabulate @(Cofree ob) (repObj @(Cofree ob) @a))

section :: forall ob a. (HasCofree ob, ob a, Ob a) => a ~> Cofree ob % a
section = index @(Cofree ob) (section' @ob id)

type CofreeSub :: forall (ob :: OB k) -> k +-> SUBCAT ob
data CofreeSub ob a b where
  CofreeSub :: (ob a) => Cofree ob a b -> CofreeSub ob (SUB a) b

instance (HasCofree ob) => Profunctor (CofreeSub ob) where
  dimap = dimapRep
  r \\ CofreeSub p = r \\ p

instance (HasCofree ob) => Representable (CofreeSub ob) where
  type CofreeSub ob % a = SUB (Cofree ob % a)
  index (CofreeSub p) = Sub (index p) \\ p
  tabulate (Sub f) = CofreeSub (tabulate f)
  repMap f = Sub (repMap @(Cofree ob) f) \\ f

instance (HasCofree ob) => Adjunction (Forget ob) (CofreeSub ob) where
  unit = unitFromRepUnit (Sub (section @ob))
  counit = counitFromRepCounit (lower @ob)