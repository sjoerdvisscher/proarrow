{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Instance.Cat where

import Data.Kind (Type)

import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Instance.Unit (Unit(..))
import Proarrow.Core (CAT, PRO, Category(..), Profunctor(..), type (~>), dimapDefault, CategoryOf)
import Proarrow.Profunctor.Identity (Id)
import Proarrow.Profunctor.Composition ((:.:))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))


newtype KIND = KIND Type
type family UNKIND (a :: KIND) :: Type where UNKIND ('KIND k) = k

type Cat :: CAT KIND
data Cat a b where
  Cat :: Profunctor (p :: PRO k1 k2) => Cat ('KIND k1) ('KIND k2)

type instance (~>) = Cat

instance Category Cat where
  type Ob c = (c ~ 'KIND (UNKIND c), Category ((~>) :: CAT (UNKIND c)))
  id = Cat @_ @_ @Id
  Cat @_ @_ @p . Cat @_ @_ @q = Cat @_ @_ @(p :.: q)

instance Profunctor Cat where
  dimap = dimapDefault
  r \\ Cat = r


type Terminate :: PRO k ()
data Terminate a b where
  Terminate :: Ob a => Terminate a '()
instance CategoryOf k => Profunctor (Terminate :: PRO k ()) where
  dimap l Unit Terminate = Terminate \\ l
  r \\ Terminate = r
instance HasTerminalObject KIND where
  type TerminalObject = 'KIND ()
  terminate' (Cat @a) = Cat @_ @_ @Terminate


type FstCat :: PRO (k1, k2) k1
data FstCat a b where
  FstCat :: Ob b => a ~> c -> FstCat '(a, b) c
instance (CategoryOf k1, CategoryOf k2) => Profunctor (FstCat :: PRO (k1, k2) k1) where
  dimap (l1 :**: l2) r (FstCat f) = FstCat (r . f . l1) \\ l2
  r \\ FstCat f = r \\ f

type SndCat :: PRO (k1, k2) k2
data SndCat a b where
  SndCat :: Ob a => b ~> c -> SndCat '(a, b) c
instance (CategoryOf k1, CategoryOf k2) => Profunctor (SndCat :: PRO (k1, k2) k2) where
  dimap (l1 :**: l2) r (SndCat f) = SndCat (r . f . l2) \\ l1
  r \\ SndCat f = r \\ f

type (:&&&:) :: PRO k1 k2 -> PRO k1 k3 -> PRO k1 (k2, k3)
data (p :&&&: q) a b where
  (:&&&:) :: p a b -> q a c -> (p :&&&: q) a '(b, c)
instance (Profunctor p, Profunctor q) => Profunctor (p :&&&: q) where
  dimap l (r1 :**: r2) (p :&&&: q) = dimap l r1 p :&&&: dimap l r2 q
  r \\ (p :&&&: q) = r \\ p \\ q

instance HasBinaryProducts KIND where
  type 'KIND l && 'KIND r = 'KIND (l, r)
  fst' Cat Cat = Cat @_ @_ @FstCat
  snd' Cat Cat = Cat @_ @_ @SndCat
  Cat @_ @_ @p &&& Cat @_ @_ @q = Cat @_ @_ @(p :&&&: q)