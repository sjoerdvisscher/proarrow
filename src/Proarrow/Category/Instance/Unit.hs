module Proarrow.Category.Instance.Unit where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))
import Proarrow.Object.Exponential (CartesianClosed(..))


data UNIT = U

type Unit :: CAT UNIT
data Unit a b where
  Unit :: Unit U U

type instance (~>) = Unit

-- | The category with one object, the terminal category.
instance Category Unit where
  type Ob a = a ~ U
  id = Unit
  Unit . Unit = Unit

instance Profunctor Unit where
  dimap = dimapDefault
  r \\ Unit = r

instance HasTerminalObject UNIT where
  type TerminalObject = U
  terminate' Unit = Unit

instance HasInitialObject UNIT where
  type InitialObject = U
  initiate' Unit = Unit

instance HasBinaryProducts UNIT where
  type U && U = U
  fst' Unit Unit = Unit
  snd' Unit Unit = Unit
  Unit &&& Unit = Unit

instance HasBinaryCoproducts UNIT where
  type U || U = U
  left' Unit Unit = Unit
  right' Unit Unit = Unit
  Unit ||| Unit = Unit

instance CartesianClosed UNIT where
  type U ~~> U = U
  curry' Unit Unit Unit = Unit
  uncurry' Unit Unit Unit = Unit
  Unit ^^^ Unit = Unit
