module Proarrow.Core where

import Data.Kind (Constraint, Type)
import Prelude (type (~))

infixr 0 ~>, :~>, +->
infixl 1 \\
infixr 0 //
infixr 9 .

-- | The kind of profunctors. Note that `j` and `k` swap places.
type j +-> k = k -> j -> Type

type CAT k = k +-> k
type OB k = k -> Constraint
type Kind = Type

class Any (a :: k)
instance Any a

class (Promonad ((~>) :: CAT k)) => CategoryOf k where
  type (~>) :: CAT k
  type Ob (a :: k) :: Constraint
  type Ob a = Any a

class (Promonad cat, CategoryOf k, cat ~ (~>) @k) => Category (cat :: CAT k)
instance (Promonad cat, CategoryOf k, cat ~ (~>) @k) => Category (cat :: CAT k)

type p :~> q = forall a b. p a b -> q a b

type Profunctor :: forall {j} {k}. j +-> k -> Constraint
class (CategoryOf j, CategoryOf k) => Profunctor (p :: j +-> k) where
  dimap :: c ~> a -> b ~> d -> p a b -> p c d
  (\\) :: ((Ob a, Ob b) => r) -> p a b -> r
  default (\\) :: (Ob a, Ob b) => ((Ob a, Ob b) => r) -> p a b -> r
  r \\ _ = r

(//) :: (Profunctor p) => p a b -> ((Ob a, Ob b) => r) -> r
p // r = r \\ p

lmap :: (Profunctor p) => c ~> a -> p a b -> p c b
lmap l p = dimap l id p \\ p

rmap :: (Profunctor p) => b ~> d -> p a b -> p a d
rmap r p = dimap id r p \\ p

dimapDefault :: (Promonad p) => p c a -> p b d -> p a b -> p c d
dimapDefault f g h = g . h . f

class (Profunctor p) => Promonad p where
  id :: (Ob a) => p a a
  (.) :: p b c -> p a b -> p a c

arr :: (Promonad p) => a ~> b -> p a b
arr f = rmap f id \\ f

type Obj a = a ~> a

obj :: forall {k} (a :: k). (CategoryOf k, Ob a) => Obj a
obj = id @_ @a

src :: forall {k} a b p. (Profunctor p) => p (a :: k) b -> Obj a
src p = obj @a \\ p

tgt :: forall {k} a b p. (Profunctor p) => p (a :: k) b -> Obj b
tgt p = obj @b \\ p

instance Profunctor (->) where
  dimap = dimapDefault

instance Promonad (->) where
  id = \a -> a
  f . g = \x -> f (g x)

-- | The category of Haskell types (a.k.a `Hask`), where the arrows are functions.
instance CategoryOf Type where
  type (~>) = (->)

-- | A helper type family to unwrap a wrapped kind.
-- This is needed because the field selector functions of newtypes have to be
-- lower case and therefore cannot be used at the type level.
type family UN (w :: j -> k) (wa :: k) :: j

-- | @Is w a@ checks that the kind @a@ is a kind wrapped by @w@.
type Is w a = a ~ w (UN w a)
