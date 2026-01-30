{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Cat where

import GHC.Base (Any)

import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), (:++:) (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , MultFtor
  , SymMonoidal (..)
  , UnitFtor
  , swap
  )
import Proarrow.Category.Monoidal.Action (Costrong (..), MonoidalAction (..), Strong (..))
import Proarrow.Category.Monoidal.Strictified ()
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..), UnOp (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (Comonoid (..), CopyDiscard, Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , diag
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  )
import Proarrow.Object.Dual (CompactClosed (..), StarAutonomous (..), compactClosedCoact)
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:))
import Proarrow.Profunctor.Identity (Id)
import Proarrow.Profunctor.Representable (Rep, Representable (..))

newtype KIND = K Kind
type instance UN K (K k) = k

type Cat :: CAT KIND
data Cat a b where
  Cat :: forall {j} {k} p. (Profunctor (p :: j +-> k)) => Cat (K j) (K k)

-- | The category of categories and profunctors between them.
instance CategoryOf KIND where
  type (~>) = Cat
  type Ob c = (Is K c, CategoryOf (UN K c))

instance Promonad Cat where
  id = Cat @Id
  Cat @p . Cat @q = Cat @(p :.: q)

instance Profunctor Cat where
  dimap = dimapDefault
  r \\ Cat = r

data family Terminate :: k +-> ()
instance (CategoryOf k) => FunctorForRep (Terminate :: k +-> ()) where
  type Terminate @ a = '()
  fmap _ = Unit
instance HasTerminalObject KIND where
  type TerminalObject = K ()
  terminate = Cat @(Rep Terminate)

data family Initiate :: VOID +-> k
instance (CategoryOf k) => FunctorForRep (Initiate :: VOID +-> k) where
  type Initiate @ a = Any
  fmap = \case {}

instance HasInitialObject KIND where
  type InitialObject = K VOID
  initiate = Cat @(Rep Initiate)

data family FstCat :: (j, k) +-> j
instance (CategoryOf j, CategoryOf k) => FunctorForRep (FstCat :: (j, k) +-> j) where
  type FstCat @ '(a, b) = a
  fmap (f :**: _) = f

data family SndCat :: (j, k) +-> k
instance (CategoryOf j, CategoryOf k) => FunctorForRep (SndCat :: (j, k) +-> k) where
  type SndCat @ '(a, b) = b
  fmap (_ :**: f) = f

type (:&&&:) :: (k +-> i) -> (k +-> j) -> (k +-> (i, j))
data (p :&&&: q) a b where
  (:&&&:) :: p a c -> q b c -> (p :&&&: q) '(a, b) c
instance (Profunctor p, Profunctor q) => Profunctor (p :&&&: q) where
  dimap (l1 :**: l2) r (p :&&&: q) = dimap l1 r p :&&&: dimap l2 r q
  r \\ (p :&&&: q) = r \\ p \\ q
instance (Representable p, Representable q) => Representable (p :&&&: q) where
  type (p :&&&: q) % a = '(p % a, q % a)
  tabulate (p :**: q) = tabulate p :&&&: tabulate q
  index (p :&&&: q) = index p :**: index q
  repMap f = repMap @p f :**: repMap @q f

instance HasBinaryProducts KIND where
  type l && r = K (UN K l, UN K r)
  withObProd r = r
  fst = Cat @(Rep FstCat)
  snd = Cat @(Rep SndCat)
  Cat @p &&& Cat @q = Cat @(p :&&&: q)

data family LftCat :: j +-> COPRODUCT j k
instance (CategoryOf j, CategoryOf k) => FunctorForRep (LftCat :: j +-> COPRODUCT j k) where
  type LftCat @ a = L a
  fmap = InjL

data family RgtCat :: k +-> COPRODUCT j k
instance (CategoryOf j, CategoryOf k) => FunctorForRep (RgtCat :: k +-> COPRODUCT j k) where
  type RgtCat @ a = R a
  fmap = InjR

type (:|||:) :: (i +-> k) -> (j +-> k) -> (COPRODUCT i j +-> k)
data (p :|||: q) a b where
  InjLP :: p a b -> (p :|||: q) a (L b)
  InjRP :: q a b -> (p :|||: q) a (R b)
instance (Profunctor p, Profunctor q) => Profunctor (p :|||: q) where
  dimap l (InjL r) (InjLP p) = InjLP (dimap l r p)
  dimap l (InjR r) (InjRP p) = InjRP (dimap l r p)
  r \\ InjLP p = r \\ p
  r \\ InjRP q = r \\ q
instance (Representable p, Representable q) => Representable (p :|||: q) where
  type (p :|||: q) % L a = p % a
  type (p :|||: q) % R a = q % a
  tabulate @b f = case obj @b of
    InjL l -> InjLP (tabulate @p f) \\ l
    InjR r -> InjRP (tabulate @q f) \\ r
  index (InjLP p) = index p
  index (InjRP q) = index q
  repMap (InjL f) = repMap @p f
  repMap (InjR f) = repMap @q f

instance HasBinaryCoproducts KIND where
  type K l || K r = K (COPRODUCT l r)
  withObCoprod r = r
  lft = Cat @(Rep LftCat)
  rgt = Cat @(Rep RgtCat)
  Cat @p ||| Cat @q = Cat @(p :|||: q)

instance MonoidalProfunctor Cat where
  par0 = id
  Cat @p `par` Cat @q = Cat @(p :**: q)

-- | Products as monoidal structure.
instance Monoidal KIND where
  type Unit = K ()
  type l ** r = K (UN K l, UN K r)
  withOb2 r = r
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

data family Swap :: (j, k) +-> (k, j)
instance (CategoryOf j, CategoryOf k) => FunctorForRep (Swap :: (j, k) +-> (k, j)) where
  type Swap @ '(a, b) = '(b, a)
  fmap (f1 :**: f2) = f2 :**: f1
instance SymMonoidal KIND where
  swap @(K j) @(K k) = Cat @(Rep Swap :: (j, k) +-> (k, j))

-- | A strictified monoidal category as a monoid in Cat.
instance (Monoidal k) => Monoid (K [k]) where
  mempty = Cat @(Rep UnitFtor)
  mappend = Cat @(Rep MultFtor)

instance (Ob a) => Comonoid (a :: KIND) where
  counit = terminate
  comult = diag
instance CopyDiscard KIND

type Curry :: (i, j) +-> k -> i +-> (OPPOSITE j, k)
data Curry p a b where
  Curry :: p c '(a, b) -> Curry p '(OP b, c) a
instance (Profunctor (p :: (i, j) +-> k), CategoryOf i, CategoryOf j) => Profunctor (Curry p :: i +-> (OPPOSITE j, k)) where
  dimap (Op l1 :**: l2) r (Curry p) = Curry (dimap l2 (r :**: l1) p) \\ r \\ l2
  r \\ Curry f = r \\ f

type Uncurry :: i +-> (OPPOSITE j, k) -> (i, j) +-> k
data Uncurry p a b where
  Uncurry :: p '(OP b, c) a -> Uncurry p c '(a, b)
instance (Profunctor (p :: i +-> (OPPOSITE j, k)), CategoryOf j, CategoryOf k) => Profunctor (Uncurry p :: (i, j) +-> k) where
  dimap l (r1 :**: r2) (Uncurry p) = Uncurry (dimap (Op r2 :**: l) r1 p)
  r \\ Uncurry f = r \\ f

instance Closed KIND where
  type K a ~~> K b = K (OPPOSITE a, b)
  withObExp r = r
  curry (Cat @p) = Cat @(Curry p)
  apply = Cat @(Uncurry Id)
  Cat @p ^^^ Cat @q = Cat @(Op q :**: p)

instance StarAutonomous KIND where
  type Dual (K a) = K (OPPOSITE a)
  dual (Cat @p) = Cat @(Op p)
  dualInv (Cat @p) = Cat @(UnOp p)
  linDist (Cat @p) = Cat @(Rep CombineDual :.: Curry p)
  linDistInv (Cat @p) = Cat @(Uncurry (Rep DistribDual :.: p))

data family CombineDual :: (OPPOSITE j, OPPOSITE k) +-> OPPOSITE (j, k)
instance (CategoryOf j, CategoryOf k) => FunctorForRep (CombineDual :: (OPPOSITE j, OPPOSITE k) +-> OPPOSITE (j, k)) where
  type CombineDual @ '(OP a, OP b) = OP '(a, b)
  fmap (Op l :**: Op r) = Op (l :**: r)

data family DistribDual :: OPPOSITE (j, k) +-> (OPPOSITE j, OPPOSITE k)
instance (CategoryOf j, CategoryOf k) => FunctorForRep (DistribDual :: OPPOSITE (j, k) +-> (OPPOSITE j, OPPOSITE k)) where
  type DistribDual @ OP '(a, b) = '(OP a, OP b)
  fmap (Op (l :**: r)) = Op l :**: Op r

data family DualUnit :: OPPOSITE () +-> ()
instance FunctorForRep (DualUnit :: OPPOSITE () +-> ()) where
  type DualUnit @ OP '() = '()
  fmap (Op Unit) = Unit

instance CompactClosed KIND where
  distribDual = Cat @(Rep DistribDual)
  dualUnit = Cat @(Rep DualUnit)

instance MonoidalAction KIND KIND where
  type Act a x = a ** x
  withObAct r = r
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator = associatorInv
  multiplicatorInv = associator

instance Strong KIND Cat where
  act = par

instance Costrong KIND Cat where
  coact @u = compactClosedCoact @u
