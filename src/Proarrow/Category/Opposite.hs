module Proarrow.Category.Opposite where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, lmap, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))

newtype OPPOSITE k = OP k
type instance UN OP (OP k) = k

type Op :: j +-> k -> OPPOSITE k +-> OPPOSITE j
data Op p a b where
  Op :: {unOp :: p b a} -> Op p (OP a) (OP b)

instance (Profunctor p) => Functor (Op p a) where
  map (Op f) (Op p) = Op (lmap f p)

instance (Profunctor p) => Profunctor (Op p) where
  dimap (Op l) (Op r) = Op . dimap r l . unOp
  r \\ Op f = r \\ f

-- | The opposite category of the category of `k`.
instance (CategoryOf k) => CategoryOf (OPPOSITE k) where
  type (~>) = Op (~>)
  type Ob a = (Is OP a, Ob (UN OP a))

instance (Promonad c) => Promonad (Op c) where
  id = Op id
  Op f . Op g = Op (g . f)

instance (HasInitialObject k) => HasTerminalObject (OPPOSITE k) where
  type TerminalObject = OP InitialObject
  terminate' (Op a) = Op (initiate' a)

instance (HasTerminalObject k) => HasInitialObject (OPPOSITE k) where
  type InitialObject = OP TerminalObject
  initiate' (Op a) = Op (terminate' a)

instance (HasBinaryCoproducts k) => HasBinaryProducts (OPPOSITE k) where
  type a && b = OP (UN OP a || UN OP b)
  fst' (Op a) (Op b) = Op (lft' a b)
  snd' (Op a) (Op b) = Op (rgt' a b)
  Op a &&& Op b = Op (a ||| b)

instance (HasBinaryProducts k) => HasBinaryCoproducts (OPPOSITE k) where
  type a || b = OP (UN OP a && UN OP b)
  lft' (Op a) (Op b) = Op (fst' a b)
  rgt' (Op a) (Op b) = Op (snd' a b)
  Op a ||| Op b = Op (a &&& b)

instance (MonoidalProfunctor p) => MonoidalProfunctor (Op p) where
  par0 = Op par0
  Op l `par` Op r = Op (l `par` r)

instance (Monoidal k) => Monoidal (OPPOSITE k) where
  type Unit = OP Unit
  type a ** b = OP (UN OP a ** UN OP b)
  leftUnitor (Op a) = Op (leftUnitorInv a)
  leftUnitorInv (Op a) = Op (leftUnitor a)
  rightUnitor (Op a) = Op (rightUnitorInv a)
  rightUnitorInv (Op a) = Op (rightUnitor a)
  associator (Op a) (Op b) (Op c) = Op (associatorInv a b c)
  associatorInv (Op a) (Op b) (Op c) = Op (associator a b c)

instance (SymMonoidal k) => SymMonoidal (OPPOSITE k) where
  swap' (Op a) (Op b) = Op (swap' b a)

instance (Comonoid c) => Monoid (OP c) where
  mempty = Op counit
  mappend = Op comult

instance (Monoid c) => Comonoid (OP c) where
  counit = Op mempty
  comult = Op mappend

instance Representable p => Corepresentable (Op p) where
  type Op p %% OP a = OP (p % a)
  coindex (Op f) = Op (index f)
  cotabulate (Op f) = Op (tabulate f)
  corepMap (Op f) = Op (repMap @p f)

instance Corepresentable p => Representable (Op p) where
  type Op p % OP a = OP (p %% a)
  index (Op f) = Op (coindex f)
  tabulate (Op f) = Op (cotabulate f)
  repMap (Op f) = Op (corepMap @p f)