{-# HLINT ignore "Use id" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Use const" #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Proarrow.Category.Instance.Constraint where

import Data.Kind (Constraint)

import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..))
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.BinaryProduct qualified as P
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Prelude (Maybe, Monoid, Semigroup)

newtype CONSTRAINT = CNSTRNT Constraint
type instance UN CNSTRNT (CNSTRNT a) = a

data (:-) a b where
  Entails :: {getEntails :: forall r. (((a) => b) => r) -> r} -> CNSTRNT a :- CNSTRNT b

instance CategoryOf CONSTRAINT where
  type (~>) = (:-)
  type Ob a = (Is CNSTRNT a)

instance Promonad (:-) where
  id = Entails \r -> r
  Entails f . Entails g = Entails \r -> f (g r)

instance Profunctor (:-) where
  dimap = dimapDefault
  r \\ Entails{} = r

instance HasTerminalObject CONSTRAINT where
  type TerminalObject = CNSTRNT ()
  terminate' Entails{} = Entails \r -> r

instance HasBinaryProducts CONSTRAINT where
  type CNSTRNT l && CNSTRNT r = CNSTRNT (l, r)
  fst' Entails{} Entails{} = Entails \r -> r
  snd' Entails{} Entails{} = Entails \r -> r
  Entails f &&& Entails g = Entails \r -> f (g r)

instance Monoidal CONSTRAINT where
  type Unit = TerminalObject
  type a ** b = a && b
  f `par` g = f *** g
  leftUnitor = P.leftUnitorProd
  leftUnitorInv = P.leftUnitorProdInv
  rightUnitor = P.rightUnitorProd
  rightUnitorInv = P.rightUnitorProdInv
  associator = P.associatorProd
  associatorInv = P.associatorProdInv

instance SymMonoidal CONSTRAINT where
  swap' Entails{} Entails{} = Entails \r -> r

class ((b) => c) => b :=> c
instance ((b) => c) => b :=> c

instance Closed CONSTRAINT where
  type CNSTRNT a ~~> CNSTRNT b = CNSTRNT (a :=> b)
  (^^^) :: forall (a :: CONSTRAINT) b x y. (b ~> y) -> (x ~> a) -> (a ~~> b) ~> (x ~~> y)
  Entails f ^^^ Entails g = Entails \r -> f (g r)
  curry' Entails{} Entails{} (Entails f) = Entails f
  uncurry' :: forall (a :: CONSTRAINT) b c. Obj b -> Obj c -> (a ~> (b ~~> c)) -> (a ** b) ~> c
  uncurry' Entails{} Entails{} (Entails f) = Entails (h @(UN CNSTRNT a) @(UN CNSTRNT b) @(UN CNSTRNT c) f)
    where
      h :: ((((x) => y :=> z) => r) -> r) -> (((x, y) => z) => r) -> r
      h g = g

-- I am solving the constraint ‘Eq a’ in a way that might turn out to loop at runtime.
-- See § Undecidable instances and loopy superclasses.
-- eqIsSuperOrd :: CNSTRNT (Ord a) :- CNSTRNT (Eq a)
-- eqIsSuperOrd = Entails \r -> r

maybeLiftsSemigroup :: CNSTRNT (Semigroup a) :- CNSTRNT (Monoid (Maybe a))
maybeLiftsSemigroup = Entails \r -> r
