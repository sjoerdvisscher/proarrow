{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.LaxFunctor where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Prelude (type (~))

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Core (CAT, CategoryOf (..))

type family Sort (kk :: CAT s) :: Type where
  Sort (kk :: CAT s) = s

-- | The kind of a tag for a lax functor. Just a way to store 'kk' and 'll'.
type (:->) :: forall s t. CAT s -> CAT t -> Type
type kk :-> ll = Proxy kk -> Proxy ll -> Type

-- | 2. Mapping of 0-cells.
type Map0 :: forall {s} {t} {kk :: CAT s} {ll :: CAT t}. (kk :-> ll) -> s -> t
type family Map0 f i

-- | 2. Mapping of 1-cells.
type Map1
  :: forall {s} {t} {kk :: CAT s} {ll :: CAT t} {i :: s} {j :: s}
   . forall (f :: kk :-> ll) -> kk i j -> ll (Map0 f i) (Map0 f j)
type family Map1 f a

-- | A Lax Functor between two bicategories.
-- 'f' is the functor tag, 'kk' is the source bicategory, and 'll' is the target.
type LaxFunctor :: forall {sk} {sl} {kk :: CAT sk} {ll :: CAT sl}. (kk :-> ll) -> Constraint
class (Bicategory kk, Bicategory ll) => LaxFunctor (f :: kk :-> ll) where
  -- | 3. Strict mapping of 2-cells.
  -- This is a strict functor on the hom-categories.
  map2
    :: forall {i} {j} (a :: kk i j) b
     . (Ob0 kk i, Ob0 kk j, Ob a, Ob b)
    => (a ~> b) -> (Map1 f a ~> Map1 f b)

  -- | 4. Lax Identity (Laxator for the unit).
  -- Note the types: from the identity of the target bicategory,
  -- to the mapped identity of the source bicategory.
  laxId
    :: forall (i :: Sort kk)
     . (Ob0 kk i)
    => I {- in ll -} ~> Map1 f (I {- in kk -} :: kk i i)

  -- | 5. Lax Composition (Laxator for tensor/composition).
  laxComp
    :: forall {i} {j} {k} (a :: kk j k) (b :: kk i j)
     . (Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob a, Ob b)
    => (Map1 f a `O` Map1 f b) ~> Map1 f (a `O` b)

  -- -----------------------------------------------------------------
  -- Constraint Propagation Proofs
  -- -----------------------------------------------------------------

  -- | Get proof that mapping a 0-cell yields a valid 0-cell in the target.
  withMap0Ob0
    :: forall (i :: Sort kk) r
     . (Ob0 kk i)
    => ((Ob0 ll (Map0 f i)) => r)
    -> r

  -- | Get proof that mapping a 1-cell yields a valid 1-cell in the target.
  withMap1Ob
    :: forall {i} {j} (a :: kk i j) r
     . (Ob0 kk i, Ob0 kk j, Ob a)
    => ((Ob (Map1 f a), Ob0 ll (Map0 f i), Ob0 ll (Map0 f j)) => r)
    -> r

class (I ~ Map1 f (I :: kk i i)) => IsNormal (f :: kk :-> ll) (i :: Sort kk)
instance (I ~ Map1 f (I :: kk i i)) => IsNormal (f :: kk :-> ll) (i :: Sort kk)

class (LaxFunctor f, forall i. (Ob0 kk i) => IsNormal f i) => NormalLaxFunctor (f :: kk :-> ll)
instance (LaxFunctor f, forall i. (Ob0 kk i) => IsNormal f i) => NormalLaxFunctor (f :: kk :-> ll)

-- Only works in GHC 9.14:
-- data family IdLax :: forall (kk :: CAT s) -> kk :-> kk
-- type instance Map0 (IdLax kk) i = i
-- type instance Map1 (IdLax kk) a = a
-- instance (Bicategory kk) => LaxFunctor (IdLax kk) where
--   map2 f = f
--   laxId = id
--   laxComp @a @b = withOb2 @kk @a @b id
--   withMap0Ob0 r = r
--   withMap1Ob r = r

-- data family MonadAsLax :: forall {kk} {a}. kk a a -> Unit :-> kk
-- type instance Map0 (MonadAsLax (t :: kk a a)) '() = a
-- type instance Map1 (MonadAsLax t) 'Unit = t
-- instance (Monad (t :: kk a a), Ob0 kk a) => LaxFunctor (MonadAsLax t) where
--   map2 Terminal = id
--   laxId = eta
--   laxComp = mu
--   withMap0Ob0 r = r
--   withMap1Ob r = r
