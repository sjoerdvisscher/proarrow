{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Cat where

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), TracedMonoidalProfunctor, trace')
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  )
import Proarrow.Object.Exponential (Closed (..), CompactClosed (..), StarAutonomous (..), compactClosedTrace')
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:))
import Proarrow.Profunctor.Identity (Id)

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

type Terminate :: k +-> ()
data Terminate a b where
  Terminate :: (Ob b) => Terminate '() b
instance (CategoryOf k) => Profunctor (Terminate :: k +-> ()) where
  dimap Unit r Terminate = Terminate \\ r
  r \\ Terminate = r
instance HasTerminalObject KIND where
  type TerminalObject = K ()
  terminate' Cat = Cat @Terminate

type FstCat :: i +-> j -> (i, k) +-> j
data FstCat p a b where
  FstCat :: (Ob c) => p a b -> FstCat p a '(b, c)
instance (CategoryOf k, Profunctor (p :: i +-> j)) => Profunctor (FstCat p :: (i, k) +-> j) where
  dimap l (r1 :**: r2) (FstCat p) = FstCat (dimap l r1 p) \\ r2
  r \\ FstCat f = r \\ f

type SndCat :: i +-> k -> (j, i) +-> k
data SndCat p a b where
  SndCat :: (Ob b) => p a c -> SndCat p a '(b, c)
instance (CategoryOf j, Profunctor (p :: i +-> k)) => Profunctor (SndCat p :: (j, i) +-> k) where
  dimap l (r1 :**: r2) (SndCat p) = SndCat (dimap l r2 p) \\ r1
  r \\ SndCat f = r \\ f

type (:&&&:) :: (k +-> i) -> (k +-> j) -> (k +-> (i, j))
data (p :&&&: q) a b where
  (:&&&:) :: p a c -> q b c -> (p :&&&: q) '(a, b) c
instance (Profunctor p, Profunctor q) => Profunctor (p :&&&: q) where
  dimap (l1 :**: l2) r (p :&&&: q) = dimap l1 r p :&&&: dimap l2 r q
  r \\ (p :&&&: q) = r \\ p \\ q

instance HasBinaryProducts KIND where
  type l && r = K (UN K l, UN K r)
  fst' (Cat @p) Cat = Cat @(FstCat p)
  snd' Cat (Cat @p) = Cat @(SndCat p)
  Cat @p &&& Cat @q = Cat @(p :&&&: q)

instance MonoidalProfunctor Cat where
  par0 = id
  Cat @p `par` Cat @q = Cat @(p :**: q)

instance Monoidal KIND where
  type Unit = K ()
  type l ** r = K (UN K l, UN K r)
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

type Swap :: h +-> i -> j +-> k -> (h, j) +-> (k, i)
data Swap p q a b where
  Swap :: p a b -> q c d -> Swap p q '(a, c) '(d, b)
instance (Profunctor p, Profunctor q) => Profunctor (Swap p q) where
  dimap (l1 :**: l2) (r1 :**: r2) (Swap p q) = Swap (dimap l1 r2 p) (dimap l2 r1 q)
  r \\ Swap p q = r \\ p \\ q
instance SymMonoidal KIND where
  swap' (Cat @p) (Cat @q) = Cat @(Swap p q)

type Curry :: (i, j) +-> k -> i +-> (k, OPPOSITE j)
data Curry p a b where
  Curry :: p c '(a, b) -> Curry p '(c, OP b) a
instance (Profunctor (p :: (i, j) +-> k), CategoryOf i, CategoryOf j) => Profunctor (Curry p :: i +-> (k, OPPOSITE j)) where
  dimap (l1 :**: Op l2) r (Curry p) = Curry (dimap l1 (r :**: l2) p) \\ r \\ l2
  r \\ Curry f = r \\ f

type Uncurry :: i +-> (k, OPPOSITE j) -> (i, j) +-> k
data Uncurry p a b where
  Uncurry :: p '(c, OP b) a -> Uncurry p c '(a, b)
instance (Profunctor (p :: i +-> (k, OPPOSITE j)), CategoryOf j, CategoryOf k) => Profunctor (Uncurry p :: (i, j) +-> k) where
  dimap l (r1 :**: r2) (Uncurry p) = Uncurry (dimap (l :**: Op r2) r1 p)
  r \\ Uncurry f = r \\ f

instance Closed KIND where
  type K a ~~> K b = K (b, OPPOSITE a)
  curry' Cat Cat (Cat @p) = Cat @(Curry p)
  uncurry' Cat Cat (Cat @p) = Cat @(Uncurry p)
  Cat @p ^^^ Cat @q = Cat @(p :**: Op q)

type DUAL k = ((), OPPOSITE k)
type Dual a = '( '(), OP a)

type DoubleNeg :: j +-> k -> DUAL (DUAL j) +-> k
data DoubleNeg p a b where
  DoubleNeg :: p a b -> DoubleNeg p a (Dual (Dual b))
instance (Profunctor p) => Profunctor (DoubleNeg p) where
  dimap l (Unit :**: Op (Unit :**: Op r)) (DoubleNeg p) = DoubleNeg (dimap l r p)
  r \\ DoubleNeg p = r \\ p
instance StarAutonomous KIND where
  type Bottom = K ()
  doubleNeg' (Cat @p) = Cat @(DoubleNeg p)

type DistribDual :: j +-> j' -> k +-> k' -> DUAL (j', k') +-> (DUAL j, DUAL k)
data DistribDual p q a b where
  DistribDual :: p c a -> q d b -> DistribDual p q '(Dual a, Dual b) (Dual '(c, d))
instance (Profunctor p, Profunctor q) => Profunctor (DistribDual p q) where
  dimap ((Unit :**: Op l1) :**: (Unit :**: Op l2)) (Unit :**: (Op (r1 :**: r2))) (DistribDual f g) =
    DistribDual (dimap r1 l1 f) (dimap r2 l2 g)
  r \\ DistribDual f g = r \\ f \\ g

instance CompactClosed KIND where
  distribDual' (Cat @p) (Cat @q) = Cat @(DistribDual p q)

instance TracedMonoidalProfunctor Cat where
  trace' = compactClosedTrace'