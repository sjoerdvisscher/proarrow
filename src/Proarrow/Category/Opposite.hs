module Proarrow.Category.Opposite where

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>), lmap)
import Proarrow.Functor (Functor(..))
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..))

newtype OP k = OP k
type family UNOP (a :: OP k) :: k where UNOP ('OP k) = k

type Op :: PRO j k -> PRO (OP k) (OP j)
data Op c a b where
  Op :: { getOp :: c b a } -> Op c ('OP a) ('OP b)

instance Profunctor p => Functor (Op p a) where
  map (Op f) (Op p) = Op (lmap f p)

instance Profunctor p => Profunctor (Op p) where
  dimap (Op l) (Op r) = Op . dimap r l . getOp
  r \\ Op f = r \\ f

type instance (~>) = Op (~>)
-- | The opposite category of category `c`.
instance Category c => Category (Op c) where
  type Ob a = (a ~ 'OP (UNOP a), Ob (UNOP a))
  id = Op id
  Op f . Op g = Op (g . f)

instance HasInitialObject k => HasTerminalObject (OP k) where
  type TerminalObject = 'OP InitialObject
  terminate' (Op a) = Op (initiate' a)

instance HasTerminalObject k => HasInitialObject (OP k) where
  type InitialObject = 'OP TerminalObject
  initiate' (Op a) = Op (terminate' a)

instance HasBinaryCoproducts k => HasBinaryProducts (OP k) where
  type 'OP a && 'OP b = 'OP (a || b)
  fst' (Op a) (Op b) = Op (left' a b)
  snd' (Op a) (Op b) = Op (right' a b)
  Op a &&& Op b = Op (a ||| b)

instance HasBinaryProducts k => HasBinaryCoproducts (OP k) where
  type 'OP a || 'OP b = 'OP (a && b)
  left' (Op a) (Op b) = Op (fst' a b)
  right' (Op a) (Op b) = Op (snd' a b)
  Op a ||| Op b = Op (a &&& b)
