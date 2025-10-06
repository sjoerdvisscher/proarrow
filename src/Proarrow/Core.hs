{-|
Description: <<===================================== Start here!
-}
module Proarrow.Core
  ( -- * Type Infrastructure
    -- ** Basic Type Definitions
    type (+->), CAT, OB, Kind
    -- ** Universal Constraint
  , Any
    -- * Category Infrastructure
    -- ** CategoryOf Class
  , CategoryOf(..)
    -- ** Category Class
  , Category
    -- * Profunctors
    -- ** Profunctor Class
  , Profunctor(..)
    -- ** Natural Transformations
  , type (:~>)
    -- ** Profunctor Utilities
  , (//), lmap, rmap
    -- ** Default Implementation
  , dimapDefault
    -- * Promonads
    -- ** Promonad Class
  , Promonad(..)
    -- ** Promonad Utilities
  , arr
    -- * Object Identities
  , Obj, obj, src, tgt
    -- * Type Family Utilities
    -- ** Kind Unwrapping
  , UN, Is
  ) where

import Data.Kind (Constraint, Type)
import Prelude (type (~))

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

-- | Alias for 'Type' for clarity in kind signatures.
type Kind = Type

-- ** Universal Constraint

-- | A constraint that's always satisfied, used as a default when no specific
-- object constraints are needed.
class Any (a :: k)
instance Any a

-- * Category Infrastructure

-- ** CategoryOf Class

-- | Establishes that @k@ is a category by specifying the morphism type and object constraints.
class (Promonad ((~>) :: CAT k)) => CategoryOf k where
  -- | The type of morphisms in the category.
  type (~>) :: CAT k
  -- | What constraints objects must satisfy.
  type Ob (a :: k) :: Constraint
  type Ob a = Any a  -- ^ Default: no constraints

-- ** Category Class

-- | A convenience class that bundles together the requirements for a well-formed category.
-- The automatic instance means you get 'Category' for free once you have 'CategoryOf' and 'Promonad'.
class (Promonad cat, CategoryOf k, cat ~ (~>) @k) => Category (cat :: CAT k)
instance (Promonad cat, CategoryOf k, cat ~ (~>) @k) => Category (cat :: CAT k)

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
  -- | Constraint elimination, extracts object constraints from a profunctor heteromorphism..
  (\\) :: ((Ob a, Ob b) => r) -> p a b -> r
  default (\\) :: (Ob a, Ob b) => ((Ob a, Ob b) => r) -> p a b -> r
  r \\ _ = r

-- ** Natural Transformations

-- | Natural transformation between profunctors.
type p :~> q = forall a b. p a b -> q a b

-- ** Profunctor Utilities

-- | Flipped version of '(\\)'.
(//) :: (Profunctor p) => p a b -> ((Ob a, Ob b) => r) -> r
p // r = r \\ p

-- | Left mapping (contravariant mapping over first argument).
lmap :: (Profunctor p) => c ~> a -> p a b -> p c b
lmap l p = dimap l id p \\ p

-- | Right mapping (covariant mapping over second argument).
rmap :: (Profunctor p) => b ~> d -> p a b -> p a d
rmap r p = dimap id r p \\ p

-- ** Default Implementation

-- | Default implementation of 'dimap' for promonads using composition.
dimapDefault :: (Promonad p) => p c a -> p b d -> p a b -> p c d
dimapDefault f g h = g . h . f

-- * Promonads

-- ** Promonad Class

-- | A promonad is a category-like profunctor with identity morphisms and composition.
--
-- __Laws:__
--
-- * Left identity: @'id' . f = f@
-- * Right identity: @f . 'id' = f@
-- * Associativity: @(h . g) . f = h . (g . f)@
class (Profunctor p) => Promonad p where
  -- | Identity morphisms.
  id :: (Ob a) => p a a
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

-- * Type Family Utilities

-- ** Kind Unwrapping

-- | A helper type family to unwrap a wrapped kind.
-- This is needed because the field selector functions of newtypes have to be
-- lower case and therefore cannot be used at the type level.
type family UN (w :: j -> k) (wa :: k) :: j

-- | @Is w a@ checks that the kind @a@ is a kind wrapped by @w@.
type Is w a = a ~ w (UN w a)
