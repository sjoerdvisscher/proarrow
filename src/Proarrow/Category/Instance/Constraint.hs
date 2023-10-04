{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT disable #-}
module Proarrow.Category.Instance.Constraint where

import Data.Kind (Constraint)
import GHC.Exts (Any)

import Proarrow.Core (UN, Is, Category(..), Profunctor(..), type (~>), dimapDefault)
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))


newtype CONSTRAINT = CNSTRNT Constraint
type instance UN CNSTNT (CNSTRNT a) = a

data (:-) a b where
  Entails :: { getEntails :: forall r. a => (b => r) -> r } -> CNSTRNT a :- CNSTRNT b

type instance (~>) = (:-)
instance Category (:-) where
  type Ob a = (Is CNSTRNT a)
  id = Entails \r -> r
  Entails f . Entails g = Entails \r -> g (f r)

instance Profunctor (:-) where
  dimap = dimapDefault
  r \\ Entails{} = r

instance HasTerminalObject CONSTRAINT where
  type TerminalObject = CNSTRNT ()
  terminate' Entails{} = Entails \r -> r

-- copied from constraints package
class Any => Bottom where
  no :: a
instance HasInitialObject CONSTRAINT where
  type InitialObject = CNSTRNT Bottom
  initiate' Entails{} = Entails \_ -> no

instance HasBinaryProducts CONSTRAINT where
  type CNSTRNT l && CNSTRNT r = CNSTRNT (l, r)
  fst' Entails{} Entails{} = Entails \r -> r
  snd' Entails{} Entails{} = Entails \r -> r
  Entails f &&& Entails g = Entails \r -> f (g r)