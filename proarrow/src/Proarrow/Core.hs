{- HLINT ignore "Redundant lambda" -}

-- | The foundational module, defining the kind-indexed category machinery everything else builds
-- on. A kind @k@ carries at most one category structure, chosen by the 'CategoryOf' class: its
-- morphism type @('~>')@ and its object constraint 'Ob' (not every type of the kind need be an
-- object). A category's identity and composition live in 'Promonad', and 'Profunctor' -- with the
-- profunctor kind @j '+->' k@ -- is this library's central generalization of functors. 'Ob'
-- constraints are typically not threaded through signatures but recovered from morphisms with
-- '(\\)' and '(//)', since an arrow is proof that its endpoints are objects.
--
-- Import "Proarrow" for the curated everyday vocabulary; this module is where that design is
-- defined, and the place to start when building your own categories.
module Proarrow.Core
  ( -- * Type Infrastructure

    -- ** Basic Type Definitions
    type (+->)
  , CAT
  , OB
  , type (:&&:)
  , Kind

    -- * Category Infrastructure

    -- ** CategoryOf Class
  , CategoryOf (..)
  , Hom
  , Ob'
  , ObId (..)

    -- * Profunctors

    -- ** Profunctor Class
  , Profunctor (..)

    -- ** Natural Transformations
  , type (:~>)

    -- ** Profunctor Utilities
  , (//)

    -- ** Default Implementation
  , dimapDefault

    -- * Promonads

    -- ** Promonad Class
  , Promonad (..)

    -- ** Promonad Utilities
  , arr

    -- * Object Identities
  , Obj
  , obj
  , src
  , tgt

    -- * Universal Constraint
  , Any
  , VacuousOb

    -- * Lifted Type Classes
  , Eq2
  , Show2

    -- * Type Family Utilities

    -- ** Kind Unwrapping
  , UN
  , Is
  , WrappedOb
  ) where

import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:) (Refl))
import Prelude (Eq, Show, type (~))

infixr 0 ~>, :~>, +->
infixl 1 \\
infixr 0 //
infixr 9 .

-- * Type Infrastructure

-- ** Basic Type Definitions

-- | The kind @j +-> k@ of profunctors from category @j@ to category @k@.
-- Note that this follows mathematical convention,
-- swapping the order compared to Haskell's contravariant-first ordering.
type j +-> k = k -> j -> Type

-- | The kind of categories on kind @k@.
type CAT k = k +-> k

-- | Object constraints for kind @k@.
type OB k = k -> Constraint

-- | The conjunction of two constraints on a common argument, as one constraint.
type (:&&:) :: OB k -> OB k -> OB k
class (c1 p, c2 p) => (c1 :&&: c2) p

instance (c1 p, c2 p) => (c1 :&&: c2) p

-- | Alias for 'Type' for clarity in kind signatures.
type Kind = Type

-- * Category Infrastructure

-- ** CategoryOf Class

-- | Establishes that @k@ is a category by specifying the morphism type and object constraints.
class (Promonad ((~>) :: CAT k)) => CategoryOf k where
  -- | The type of morphisms in the category.
  type (~>) :: CAT k

  -- | What constraints objects must satisfy. Defaults to 'ObId', which is what a category with
  -- more than one object wants; a category where every type of the kind is an object, with no
  -- evidence needed, says @type 'Ob' a = 'Any' a@ instead.
  type Ob (a :: k) :: Constraint

  type Ob a = ObId a

-- | A type synonym for @(~>) :: CAT k@, the type of morphisms in the category of kind @k@.
type Hom k = ((~>) :: CAT k)

-- | 'Ob' as a proper class, for the positions where the type family 'Ob' itself cannot appear,
-- such as the head of a quantified constraint.
class (Ob a, CategoryOf k) => Ob' (a :: k)

instance (Ob a, CategoryOf k) => Ob' (a :: k)

-- | Objecthood that carries the object's own identity arrow, and the default for 'Ob'.
--
-- This is what a category with more than one object needs: 'id' must produce the identity /at
-- whichever object it is asked for/, so it has to dispatch on the object, and one instance per
-- object is exactly that dispatch. Since 'Ob' defaults to 'ObId' and 'id' defaults to 'objId',
-- such a category defines neither -- it just gives an 'ObId' instance per object:
--
-- > type data STATE = Draft | Live
-- >
-- > type Move :: CAT STATE
-- > data Move a b where
-- >   KeepDraft :: Move Draft Draft
-- >   Publish :: Move Draft Live
-- >   KeepLive :: Move Live Live
-- >
-- > instance ObId Draft where objId = KeepDraft
-- > instance ObId Live where objId = KeepLive
-- >
-- > instance CategoryOf STATE where
-- >   type (~>) = Move
type ObId :: forall {k}. k -> Constraint
class (CategoryOf k) => ObId (a :: k) where
  -- | The identity arrow at @a@.
  objId :: a ~> a

-- * Profunctors

-- ** Profunctor Class

-- | The core profunctor abstraction. A profunctor is contravariant in its first
-- argument and covariant in its second argument.
--
-- __Laws:__
--
-- * @'dimap' 'id' 'id' = 'id'@
-- * @'dimap' (f . g) (h . i) = 'dimap' g h . 'dimap' f i@
type Profunctor :: forall {j} {k}. j +-> k -> Constraint
class (CategoryOf j, CategoryOf k) => Profunctor (p :: j +-> k) where
  -- | Map contravariantly over the first argument and covariantly over the second.
  dimap :: c ~> a -> b ~> d -> p a b -> p c d
  dimap l r = lmap l . rmap r

  -- | Left mapping (contravariant mapping over first argument).
  lmap :: c ~> a -> p a b -> p c b
  lmap l p = dimap l id p \\ p

  -- | Right mapping (covariant mapping over second argument).
  rmap :: b ~> d -> p a b -> p a d
  rmap r p = dimap id r p \\ p

  -- | Constraint elimination, extracts object constraints from a profunctor heteromorphism.
  (\\) :: ((Ob a, Ob b) => r) -> p a b -> r
  default (\\) :: (Ob a, Ob b) => ((Ob a, Ob b) => r) -> p a b -> r
  r \\ _ = r

  {-# MINIMAL dimap | (lmap, rmap) #-}

-- ** Natural Transformations

-- | Natural transformation between profunctors.
type p :~> q = forall a b. p a b -> q a b

-- ** Profunctor Utilities

-- | Flipped version of '(\\)'.
(//) :: (Profunctor p) => p a b -> ((Ob a, Ob b) => r) -> r
p // r = r \\ p

-- ** Default Implementation

-- | Default implementation of 'dimap' for promonads using composition.
dimapDefault :: (Promonad p) => p c a -> p b d -> p a b -> p c d
dimapDefault f g h = g . h . f

-- * Promonads

-- ** Promonad Class

-- | A promonad is a category-like profunctor with identity morphisms and composition.
--
-- This is also known as a category structure, or an identity-on-objects functor.
--
-- __Laws:__
--
-- * Left identity: @'id' . f = f@
-- * Right identity: @f . 'id' = f@
-- * Associativity: @(h . g) . f = h . (g . f)@
type Promonad :: forall {k}. CAT k -> Constraint
class (Profunctor p) => Promonad (p :: CAT k) where
  -- | Identity morphisms.
  --
  -- Defaults to 'objId' for a category's own hom-profunctor, so a category that leaves 'Ob' at
  -- its 'ObId' default gets 'id' for free.
  id :: (Ob a) => p a a
  default id :: forall (a :: k). (ObId a, p ~ ((~>) :: CAT k)) => p a a
  id = objId

  -- | Composition (note the parameter order matches function composition).
  (.) :: p b c -> p a b -> p a c

-- ** Promonad Utilities

-- | Lifts morphisms from the base category into the promonad.
arr :: (Promonad p) => a ~> b -> p a b
arr f = rmap f id \\ f

-- * Object Identities

-- | Type of identity morphism for object @a@.
type Obj a = a ~> a

-- | The identity morphism for a given object.
-- Compared to @id@ this makes the kind argument implicit,
-- allowing to write @obj \@a@ instead of @id \@k \@a@.
obj :: forall {k} (a :: k). (CategoryOf k, Ob a) => Obj a
obj = id @_ @a

-- | Extract source identity morphism from a profunctor heteromorphism.
src :: forall {k} a b p. (Profunctor p) => p (a :: k) b -> Obj a
src p = obj @a \\ p

-- | Extract target identity morphism from a profunctor heteromorphism.
tgt :: forall {k} a b p. (Profunctor p) => p (a :: k) b -> Obj b
tgt p = obj @b \\ p

-- * Standard Instances

instance Profunctor (->) where
  dimap = dimapDefault

instance Promonad (->) where
  id = \a -> a
  f . g = \x -> f (g x)

-- | The category of Haskell types (a.k.a @Hask@), where the arrows are functions.
instance CategoryOf Type where
  type (~>) = (->)
  type Ob a = Any a

instance (VacuousOb k, Hom k ~ (:~:)) => Profunctor ((:~:) :: CAT k) where
  dimap Refl Refl Refl = Refl

instance (VacuousOb k, Hom k ~ (:~:)) => Promonad ((:~:) :: CAT k) where
  id = Refl
  Refl . Refl = Refl

-- * Universal Constraint

-- | A constraint that's always satisfied, used as a default when no specific
-- object constraints are needed.
class Any (a :: k)

instance Any a

-- | A category without constraints on its objects.
class (CategoryOf k, forall a. Ob' (a :: k)) => VacuousOb k

instance (CategoryOf k, forall a. Ob' (a :: k)) => VacuousOb k

-- | A profunctor (or something of that kind) whose elements can be compared.
class (forall x y. Eq (p x y)) => Eq2 p

instance (forall x y. Eq (p x y)) => Eq2 p

-- | A profunctor (or something of that kind) whose elements can be shown.
class (forall x y. Show (p x y)) => Show2 p

instance (forall x y. Show (p x y)) => Show2 p

-- * Type Family Utilities

-- ** Kind Unwrapping

-- | A helper type family to unwrap a wrapped kind @w x@.
type UN :: (j -> k) -> k -> j
type family UN w wa where
  UN w (w x) = x

-- | @Is w a@ checks that the kind @a@ is a kind wrapped by @w@.
type Is w a = a ~ w (UN w a)

-- | @WrappedOb w a@ asserts both that @a@ is wrapped by @w@ ('Is' @w a@)
-- and that its unwrapped kind satisfies @Ob@.
type WrappedOb :: (j -> k) -> k -> Constraint
type WrappedOb w a = (Is w a, Ob (UN w a))
