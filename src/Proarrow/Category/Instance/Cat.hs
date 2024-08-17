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

type FstCat :: (j, k) +-> j
data FstCat a b where
  FstCat :: (Ob c) => a ~> b -> FstCat a '(b, c)
instance (CategoryOf j, CategoryOf k) => Profunctor (FstCat :: (j, k) +-> j) where
  dimap l (r1 :**: r2) (FstCat f) = FstCat (r1 . f . l) \\ r2
  r \\ FstCat f = r \\ f

type SndCat :: (j, k) +-> k
data SndCat a b where
  SndCat :: (Ob b) => a ~> c -> SndCat a '(b, c)
instance (CategoryOf j, CategoryOf k) => Profunctor (SndCat :: (j, k) +-> k) where
  dimap l (r1 :**: r2) (SndCat f) = SndCat (r2 . f . l) \\ r1
  r \\ SndCat f = r \\ f

type (:&&&:) :: (k +-> i) -> (k +-> j) -> (k +-> (i, j))
data (p :&&&: q) a b where
  (:&&&:) :: p a c -> q b c -> (p :&&&: q) '(a, b) c
instance (Profunctor p, Profunctor q) => Profunctor (p :&&&: q) where
  dimap (l1 :**: l2) r (p :&&&: q) = dimap l1 r p :&&&: dimap l2 r q
  r \\ (p :&&&: q) = r \\ p \\ q

instance HasBinaryProducts KIND where
  type K l && K r = K (l, r)
  fst' Cat Cat = Cat @_ @_ @FstCat
  snd' Cat Cat = Cat @_ @_ @SndCat
  Cat @_ @_ @p &&& Cat @_ @_ @q = Cat @_ @_ @(p :&&&: q)
