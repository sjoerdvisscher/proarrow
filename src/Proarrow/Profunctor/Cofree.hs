{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Cofree where

import Data.Kind (Constraint)
import Prelude (Int, fst, snd)

import Proarrow.Category.Instance.Sub (Forget, SUBCAT (..), Sub (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..))
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Representable (Representable (..), repUniv)

type HasCofree :: forall {k}. OB k -> Constraint
class (CategoryOf k, forall a. (Ob a) => ob (Cofree ob a)) => HasCofree (ob :: k -> Constraint) where
  type Cofree ob (a :: k) :: k
  lower :: (Ob a) => Cofree ob a ~> a
  unfoldMap :: (ob a) => a ~> b -> a ~> Cofree ob b

section :: forall ob a. (HasCofree ob, ob a, Ob a) => a ~> Cofree ob a
section = unfoldMap @ob id

cofreeMap :: (HasCofree ob) => (a ~> b) -> Cofree ob a ~> Cofree ob b
cofreeMap @ob f = unfoldMap @ob (f . lower @ob) \\ f

cofreeComp :: (HasCofree ob, Ob a) => Cofree ob b ~> c -> Cofree ob a ~> b -> Cofree ob a ~> c
cofreeComp @ob l r = l . unfoldMap @ob r

-- | By creating the right adjoint to the forgetful functor,
-- we obtain the forgetful-cofree adjunction.
instance (HasCofree ob) => Representable (Corep (Forget (ob :: OB k))) where
  type Corep (Forget ob) % a = SUB (Cofree ob a)
  index (Corep f) = Sub (unfoldMap @ob f) \\ f
  repUniv @a = let f = lower @ob @a in Corep f \\ f

class Test a where
  test :: a -> Int
instance HasCofree Test where
  type Cofree Test a = (Int, a)
  lower = snd
  unfoldMap f a = (test a, f a)
instance Promonad (Costar ((,) Int)) where
  id = Costar (lower @Test)
  Costar l . Costar r = Costar (cofreeComp @Test l r)
instance Test (Int, a) where
  test = fst