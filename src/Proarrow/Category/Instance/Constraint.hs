{-# HLINT ignore "Use id" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Use const" #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Proarrow.Category.Instance.Constraint where

import Data.Kind (Constraint)
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.BinaryProduct qualified as P
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))

newtype CONSTRAINT = CNSTRNT Constraint
type instance UN CNSTRNT (CNSTRNT a) = a

data (:-) a b where
  Entails :: {unEntails :: forall r. (((a) => b) => r) -> r} -> CNSTRNT a :- CNSTRNT b

instance CategoryOf CONSTRAINT where
  type (~>) = (:-)
  type Ob a = (Is CNSTRNT a)

instance Promonad (:-) where
  id = Entails \r -> r
  Entails f . Entails g = Entails \r -> f (g r)

instance Profunctor (:-) where
  dimap = dimapDefault
  r \\ Entails{} = r

instance ThinProfunctor (:-) where
  type HasArrow (:-) (CNSTRNT a) (CNSTRNT b) = a :=> b
  arr = Entails \r -> r
  withArr (Entails f) r = f r

instance HasTerminalObject CONSTRAINT where
  type TerminalObject = CNSTRNT ()
  terminate = Entails \r -> r

instance HasBinaryProducts CONSTRAINT where
  type CNSTRNT l && CNSTRNT r = CNSTRNT (l, r)
  withObProd r = r
  fst = Entails \r -> r
  snd = Entails \r -> r
  Entails f &&& Entails g = Entails \r -> f (g r)

instance MonoidalProfunctor (:-) where
  par0 = id
  f `par` g = f *** g

instance Monoidal CONSTRAINT where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 r = r
  leftUnitor = P.leftUnitorProd
  leftUnitorInv = P.leftUnitorProdInv
  rightUnitor = P.rightUnitorProd
  rightUnitorInv = P.rightUnitorProdInv
  associator = P.associatorProd
  associatorInv = P.associatorProdInv

instance SymMonoidal CONSTRAINT where
  swap = Entails \r -> r

instance Monoid (CNSTRNT ()) where
  mempty = id
  mappend = Entails \r -> r

instance Comonoid (CNSTRNT a) where
  counit = Entails \r -> r
  comult = Entails \r -> r

class ((b) => c) => b :=> c
instance ((b) => c) => b :=> c

instance Closed CONSTRAINT where
  type CNSTRNT a ~~> CNSTRNT b = CNSTRNT (a :=> b)
  withObExp r = r
  Entails f ^^^ Entails g = Entails \r -> f (g r)
  curry (Entails f) = Entails f
  uncurry @b @c @a (Entails f) = Entails (h @(UN CNSTRNT a) @(UN CNSTRNT b) @(UN CNSTRNT c) f)
    where
      h :: ((((x) => y :=> z) => r) -> r) -> (((x, y) => z) => r) -> r
      h g = g

-- I am solving the constraint ‘Eq a’ in a way that might turn out to loop at runtime.
-- See § Undecidable instances and loopy superclasses.
-- eqIsSuperOrd :: CNSTRNT (P.Ord a) :- CNSTRNT (P.Eq a)
-- eqIsSuperOrd = Entails \r -> r

maybeLiftsSemigroup :: CNSTRNT (P.Semigroup a) :- CNSTRNT (Monoid (P.Maybe a))
maybeLiftsSemigroup = Entails \r -> r
