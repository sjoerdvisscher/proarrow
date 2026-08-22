{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The monoidal category of endo-profunctors on @k@ under composition ('(:.:)'\/'Id'),
-- with functor composition as the tensor. This is the profunctor-specific counterpart of
-- "Proarrow.Category.Monoidal.Endo" (in @proarrow-equipment@, which builds the analogous
-- structure for an arbitrary 'Proarrow.Bicategory.Bicategory'), hardcoded here to
-- @Prof@\/@:.:@\/'Id' instead, and reusing "Proarrow.Path"\'s associators\/unitors so they
-- aren't proved twice.
--
-- Note this is a genuinely different monoidal structure on @k +-> k@ than
-- "Proarrow.Profunctor.Instance.Day"\'s @Monoidal (j +-> k)@ instance (Day convolution) --
-- hence the need for a fresh wrapper type rather than another instance for the same kind.
module Proarrow.Category.Monoidal.Endo where

import Data.Kind (Constraint, Type)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..))
import Proarrow.Category.Monoidal.Distributive (Traversable)
import Proarrow.Core (CAT, CategoryOf (..), Is, OB, Profunctor (..), Promonad (..), UN, type (+->), type (:~>))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Optic (type (:&&:))
import Proarrow.Path qualified as Path
import Proarrow.Profunctor.Instance.Composition (o, (:.:))
import Proarrow.Profunctor.Instance.Identity (Id)
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), index, repMap, repUniv, withObRep)

-- | An object of @'ENDO' k@ is an endo-profunctor @k +-> k@, i.e. (not necessarily
-- representable) a functor @k -> k@ under the profunctor encoding.
type ENDO :: Type -> Type
type data ENDO k = E (k +-> k)

-- | Morphisms of @'ENDO' k@ are natural transformations between the underlying profunctors.
type Endo :: CAT (ENDO k)
data Endo p q where
  Endo :: (Profunctor p, Profunctor q) => (p :~> q) -> Endo (E p) (E q)

instance (CategoryOf k) => Profunctor (Endo :: CAT (ENDO k)) where
  dimap (Endo l) (Endo r) (Endo f) = Endo (r . f . l)
  r \\ Endo _ = r

instance (CategoryOf k) => Promonad (Endo :: CAT (ENDO k)) where
  id = Endo Path.idN
  Endo f . Endo g = Endo (f . g)

instance (CategoryOf k) => CategoryOf (ENDO k) where
  type (~>) = Endo
  type Ob (a :: ENDO k) = (Is E a, Profunctor (UN E a))

instance (CategoryOf k) => MonoidalProfunctor (Endo :: CAT (ENDO k)) where
  one = Endo Path.idN
  Endo f ** Endo g = Endo (f `o` g)

instance (CategoryOf k) => Monoidal (ENDO k) where
  type Unit = E Id
  type E p ** E q = E (p :.: q)
  withOb2 @(E _) @(E _) r = r
  leftUnitor @(E p) = Endo (Path.leftUnitor @p)
  leftUnitorInv @(E p) = Endo (Path.leftUnitorInv @p)
  rightUnitor @(E p) = Endo (Path.rightUnitor @p)
  rightUnitorInv @(E p) = Endo (Path.rightUnitorInv @p)
  associator @(E p) @(E q) @(E r) = Endo (Path.associator @p @q @r)
  associatorInv @(E p) @(E q) @(E r) = Endo (Path.associatorInv @p @q @r)

-- | Lift a constraint on profunctors @k +-> k@ to the corresponding 'ENDO' objects.
type OnE :: ((k +-> k) -> Constraint) -> ENDO k -> Constraint
class (Is E a, c (UN E a)) => OnE c a

instance (Is E a, c (UN E a)) => OnE c a

-- | The subcategory of representable, traversable endo-profunctors -- exactly the
-- functors 'Proarrow.Category.Monoidal.Distributive.repTraverse' can traverse with.
-- 'Monoidal' for free via "Proarrow.Category.Instance.Sub"\'s generic
-- @Monoidal (SUBCAT ob)@, since both 'Representable' and 'Traversable' already have
-- instances closing them under @:.:@\/'Id'.
type TravSub k = SUBCAT (OnE (Representable :&&: Traversable) :: OB (ENDO k))

-- | The action of 'TravSub' on @k@ by application: @'Act' 'TravAction' ('SUB' ('E' f)) x = f '%' x@.
type TravAction = Rep TravAction'

data family TravAction' :: (TravSub k, k) +-> k
instance (CategoryOf k) => FunctorForRep (TravAction' :: (TravSub k, k) +-> k) where
  type TravAction' @ '(SUB (E p), x) = p % x
  fmap (Sub (Endo @p @q n) :**: (g :: x ~> y)) = index @q (n (repUniv @p @y)) . repMap @p g \\ g

instance (CategoryOf k) => MonoidalAction (TravAction :: (TravSub k, k) +-> k) where
  unitor = id
  unitorInv = id
  multiplicator @(SUB (E p)) @(SUB (E q)) @x = withObRep @q @x (withObRep @p @(q % x) id)
  multiplicatorInv @(SUB (E p)) @(SUB (E q)) @x = withObRep @q @x (withObRep @p @(q % x) id)
