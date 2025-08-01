module Proarrow.Category.Opposite where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, lmap, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Copower (Copowered (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Power (Powered (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))

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
  terminate = Op initiate

instance (HasTerminalObject k) => HasInitialObject (OPPOSITE k) where
  type InitialObject = OP TerminalObject
  initiate = Op terminate

instance (HasBinaryCoproducts k) => HasBinaryProducts (OPPOSITE k) where
  type a && b = OP (UN OP a || UN OP b)
  withObProd @(OP a) @(OP b) = withObCoprod @k @a @b
  fst @(OP a) @(OP b) = Op (lft @_ @a @b)
  snd @(OP a) @(OP b) = Op (rgt @_ @a @b)
  Op a &&& Op b = Op (a ||| b)

instance (HasBinaryProducts k) => HasBinaryCoproducts (OPPOSITE k) where
  type a || b = OP (UN OP a && UN OP b)
  withObCoprod @(OP a) @(OP b) = withObProd @k @a @b
  lft @(OP a) @(OP b) = Op (fst @_ @a @b)
  rgt @(OP a) @(OP b) = Op (snd @_ @a @b)
  Op a ||| Op b = Op (a &&& b)

instance (MonoidalProfunctor p) => MonoidalProfunctor (Op p) where
  par0 = Op par0
  Op l `par` Op r = Op (l `par` r)

-- | The opposite of a monoidal category is also monoidal, with the same tensor product.
instance (Monoidal k) => Monoidal (OPPOSITE k) where
  type Unit = OP Unit
  type a ** b = OP (UN OP a ** UN OP b)
  withOb2 @(OP a) @(OP b) = withOb2 @k @a @b
  leftUnitor = Op leftUnitorInv
  leftUnitorInv = Op leftUnitor
  rightUnitor = Op rightUnitorInv
  rightUnitorInv = Op rightUnitor
  associator @(OP a) @(OP b) @(OP c) = Op (associatorInv @k @a @b @c)
  associatorInv @(OP a) @(OP b) @(OP c) = Op (associator @k @a @b @c)

instance (SymMonoidal k) => SymMonoidal (OPPOSITE k) where
  swap @(OP a) @(OP b) = Op (swap @k @b @a)

instance (Comonoid c) => Monoid (OP c) where
  mempty = Op counit
  mappend = Op comult

instance (Monoid c) => Comonoid (OP c) where
  counit = Op mempty
  comult = Op mappend

instance (Representable p) => Corepresentable (Op p) where
  type Op p %% OP a = OP (p % a)
  coindex (Op f) = Op (index f)
  cotabulate (Op f) = Op (tabulate f)
  corepMap (Op f) = Op (repMap @p f)

instance (Corepresentable p) => Representable (Op p) where
  type Op p % OP a = OP (p %% a)
  index (Op f) = Op (coindex f)
  tabulate (Op f) = Op (cotabulate f)
  repMap (Op f) = Op (corepMap @p f)

type UnOp :: OPPOSITE k +-> OPPOSITE j -> j +-> k
data UnOp p a b where
  UnOp :: {unUnOp :: p (OP b) (OP a)} -> UnOp p a b
instance (CategoryOf j, CategoryOf k, Profunctor p) => Profunctor (UnOp p :: j +-> k) where
  dimap l r = UnOp . dimap (Op r) (Op l) . unUnOp
  r \\ UnOp f = r \\ f

instance (Strong k p) => Strong (OPPOSITE k) (Op p) where
  act (Op w) (Op p) = Op (act w p)
instance (MonoidalAction m k) => MonoidalAction (OPPOSITE m) (OPPOSITE k) where
  type Act (OP a) (OP b) = OP (Act a b)
  withObAct @(OP a) @(OP b) = withObAct @m @k @a @b
  unitor = Op (unitorInv @m)
  unitorInv = Op (unitor @m)
  multiplicator @(OP a) @(OP b) @(OP x) = Op (multiplicatorInv @m @k @a @b @x)
  multiplicatorInv @(OP a) @(OP b) @(OP x) = Op (multiplicator @m @k @a @b @x)

instance (Copowered k) => Powered (OPPOSITE k) where
  type OP a ^ n = OP (n *. a)
  withObPower @(OP a) @n = withObCopower @k @a @n
  power f = Op (copower (unOp . f))
  unpower (Op f) n = Op (uncopower f n)

instance (Powered k) => Copowered (OPPOSITE k) where
  type n *. OP a = OP (a ^ n)
  withObCopower @(OP a) @n = withObPower @k @a @n
  copower f = Op (power (unOp . f))
  uncopower (Op f) n = Op (unpower f n)

instance (ThinProfunctor p) => ThinProfunctor (Op p) where
  type HasArrow (Op p) (OP a) (OP b) = HasArrow p b a
  arr = Op arr
  withArr (Op f) r = withArr f r
