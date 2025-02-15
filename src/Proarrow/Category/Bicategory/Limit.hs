{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Limit where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf (..), Obj)
import Proarrow.Category.Bicategory (Bicategory(..))

type family TerminalObject (kk :: CAT s) :: s
type HasTerminalObject :: forall {s}. CAT s -> Constraint
class HasTerminalObject (kk :: CAT s) where
  type Terminate kk (j :: s) :: kk j (TerminalObject kk)
  terminate :: Ob0 kk j => Obj (Terminate kk j)
  termUniv :: (Ob0 kk j, Ob f, Ob g) => (f :: kk j (TerminalObject kk)) ~> (g :: kk j (TerminalObject kk))

type family Product (kk :: CAT s) (a :: s) (b :: s) :: s
type HasBinaryProducts :: forall {s}. CAT s -> Constraint
class HasBinaryProducts (kk :: CAT s) where
  type Fst kk (a :: s) (b :: s) :: kk (Product kk a b) a
  type Snd kk (a :: s) (b :: s) :: kk (Product kk a b) b
  fstObj :: (Ob0 kk a, Ob0 kk b) => Obj (Fst kk a b)
  sndObj :: (Ob0 kk a, Ob0 kk b) => Obj (Snd kk a b)
  type (&&&) (f :: kk j a) (g :: kk j b) :: kk j (Product kk a b)
  prodObj :: (Ob0 kk j, Ob0 kk a, Ob0 kk b, Ob (f :: kk j a), Ob (g :: kk j b)) => Obj (f &&& g)
  prodUniv :: (Ob0 kk j, Ob0 kk a, Ob0 kk b, Ob (h :: kk j (Product kk a b)), Ob (k :: kk j (Product kk a b)))
    => (Fst kk a b `O` h ~> Fst kk a b `O` k) -> (Snd kk a b `O` h ~> Snd kk a b `O` k) -> h ~> k
