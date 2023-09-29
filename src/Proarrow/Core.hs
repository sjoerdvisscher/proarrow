{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant lambda" #-}
{-# HLINT ignore "Avoid lambda" #-}
module Proarrow.Core where

import Data.Kind (Type, Constraint)

infixr 0 ~>, :~>
infixl 1 \\
infixr 0 //
infixr 9 .

type PRO j k = j -> k -> Type
type CAT k = PRO k k
type BI k = (k, k) -> k
type OB k = k -> Constraint

type Category :: CAT k -> Constraint
class (Profunctor cat, (~>) ~ cat) => Category (cat :: CAT k) where
  type Ob (a :: k) :: Constraint
  type Ob a = ()
  id :: Ob a => cat a a
  (.) :: cat b c -> cat a b -> cat a c

type family (~>) :: CAT k
type CategoryOf k = Category ((~>) :: CAT k)

type p :~> q = forall a b. p a b ~> q a b

type Profunctor :: forall {j} {k}. PRO j k -> Constraint
class (CategoryOf j, CategoryOf k) => Profunctor (p :: PRO j k) where
  dimap :: c ~> a -> b ~> d -> p a b -> p c d
  (\\) :: ((Ob a, Ob b) => r) -> p a b -> r
  default (\\) :: (Ob a, Ob b) => ((Ob a, Ob b) => r) -> p a b -> r
  r \\ _ = r

(//) :: Profunctor p => p a b -> ((Ob a, Ob b) => r) -> r
p // r = r \\ p

lmap :: Profunctor p => c ~> a -> p a b -> p c b
lmap l p = dimap l id p \\ p

rmap :: Profunctor p => b ~> d -> p a b -> p a d
rmap r p = dimap id r p \\ p

dimapDefault :: CategoryOf k => (c :: k) ~> a -> (b :: k) ~> d -> a ~> b -> c ~> d
dimapDefault f g h = g . h . f


type instance (~>) = (->)

instance Category (->) where
  id = \a -> a
  f . g = \x -> f (g x)

instance Profunctor (->) where
  dimap = dimapDefault
