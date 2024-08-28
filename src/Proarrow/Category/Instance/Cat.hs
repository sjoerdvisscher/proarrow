{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Cat where

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:))
import Proarrow.Profunctor.Identity (Id)

newtype KIND = K Kind
type instance UN K (K k) = k

type Cat :: CAT KIND
data Cat a b where
  Cat :: (Profunctor (p :: j +-> k)) => Cat (K j) (K k)

-- | The category of categories and profunctors between them.
instance CategoryOf KIND where
  type (~>) = Cat
  type Ob c = (Is K c, CategoryOf (UN K c))

instance Promonad Cat where
  id = Cat @_ @_ @Id
  Cat @_ @_ @p . Cat @_ @_ @q = Cat @_ @_ @(p :.: q)

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
  terminate' Cat = Cat @_ @_ @Terminate

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
  type K l && K r = K (l, r)
  fst' (Cat @_ @_ @p) Cat = Cat @_ @_ @(FstCat p)
  snd' Cat (Cat @_ @_ @p) = Cat @_ @_ @(SndCat p)
  Cat @_ @_ @p &&& Cat @_ @_ @q = Cat @_ @_ @(p :&&&: q)
