{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Relative where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf(..), CAT)
import Proarrow.Category.Bicategory (Bicategory(..))

-- | A @j@-relative monad @t@. Note that @j@ is the opposite of the usual convention.
-- See 'Proarrow.Squares.Relative' how to use this with a conjoint and a companion to get the regular definition.
type Monad :: forall {s} {kk :: CAT s} {a :: s} {e :: s}. kk e a -> kk a e -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk e, Ob j, Ob t) => Monad (j :: kk e a) (t :: kk a e) where
  unit :: I ~> j `O` t
  mult :: t `O` j `O` t ~> t

type Algebra :: forall {s} {kk :: CAT s} {a :: s} {d :: s} {e :: s}. kk e a -> kk a e -> kk d e -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk d, Ob0 kk e, Ob j, Ob t) => Algebra (j :: kk e a) (t :: kk a e) (car :: kk d e) where
  act :: t `O` j `O` car ~> car

type Opalgebra :: forall {s} {kk :: CAT s} {a :: s} {b :: s} {e :: s}. kk e a -> kk a e -> kk a b -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk b, Ob0 kk e, Ob j, Ob t) => Opalgebra (j :: kk e a) (t :: kk a e) (car :: kk a b) where
  opact :: car `O` j `O` t ~> car

type Adjunction :: forall {s} {kk :: CAT s} {a} {c} {e}. kk e a -> kk a c -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk c, Ob0 kk e, Ob j, Ob l, Ob r) => Adjunction (j :: kk e a) (l :: kk a c) (r :: kk c e) where
  eta :: I ~> j `O` r `O` l
  epsilon :: l `O` j `O` r ~> I

type Comonad :: forall {s} {kk :: CAT s} {a :: s} {e :: s}. kk e a -> kk a e -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk e, Ob j, Ob t) => Comonad (j :: kk e a) (t :: kk a e) where
  counit :: j `O` t ~> I
  comult :: t ~> t `O` j `O` t

type Coalgebra :: forall {s} {kk :: CAT s} {a :: s} {d :: s} {e :: s}. kk e a -> kk a e -> kk d e -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk d, Ob0 kk e, Ob j, Ob t) => Coalgebra (j :: kk e a) (t :: kk a e) (car :: kk d e) where
  coact :: car ~> t `O` j `O` car

type Coopalgebra :: forall {s} {kk :: CAT s} {a :: s} {b :: s} {e :: s}. kk e a -> kk a e -> kk a b -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk b, Ob0 kk e, Ob j, Ob t) => Coopalgebra (j :: kk e a) (t :: kk a e) (car :: kk a b) where
  coopact :: car ~> car `O` j `O` t

type Coadjunction :: forall {s} {kk :: CAT s} {a} {c} {e}. kk e a -> kk a c -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk a, Ob0 kk c, Ob0 kk e) => Coadjunction (j :: kk e a) (l :: kk a c) (r :: kk c e) where
  coeta :: j `O` r `O` l ~> I
  coepsilon :: I ~> l `O` j `O` r
