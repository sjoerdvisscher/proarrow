{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Laws stated as code, polymorphic in the category. A law of the structures @cs@ takes five
-- object variables and a supply of named arbitrary arrows, and returns an equation between two
-- arrows. The @proarrow:testing@ library checks laws by running them with random objects and
-- arrows, in a category whose arrows also carry their own description, so that a failing law
-- prints as the code it was built from.
--
-- A derived operation (a function defined from the class methods, like
-- 'Proarrow.Category.Monoidal.StarAutonomous.doubleNeg') would print as its definition. 'label'
-- names it instead.
--
-- A class's laws are an instance of 'Laws' for the list of structures they mention, the same list
-- the class's free-category structure requires, e.g.
-- @'Laws' 'Proarrow.Category.Monoidal.SymMonoidalStructures'@. The instances live next to their
-- classes.
module Proarrow.Tools.Laws where

import Data.Kind (Constraint, Type)
import Prelude (Applicative, Monad, String, pure, (++))

import Proarrow.Category.Instance.Free (All)
import Proarrow.Core (CategoryOf (..), Kind, Profunctor (..), Promonad (..))

-- * Laws

-- | The laws of the structures @cs@. A class with a new kind of object also needs support in the
-- testing library before its laws can be checked, see "Proarrow.Testing.Laws.Run".
--
-- For example, the laws of a functor on objects @Sq@ with action @sq@ on arrows:
--
-- @
-- instance Laws '[HasSquare] where
--   laws =
--     [ Law "sq identity" \\ \@a _ -> withObSq \@_ \@a (sq (obj \@a) '=:=' id)
--     , Law "sq composition" \\ \@a \@b \@c gen -> do
--         f <- gen \@a \@b "f"
--         g <- gen \@b \@c "g"
--         sq (g . f) '=:=' sq g . sq f
--     ]
-- @
type Laws :: [Kind -> Constraint] -> Constraint
class Laws cs where
  -- | The laws, each tested as its own property.
  laws :: [Law cs]

-- | A named law.
type Law :: [Kind -> Constraint] -> Type
data Law cs = Law String (LawBody cs Equation)

-- | The name of a law, used as its test's name.
lawName :: Law cs -> String
lawName (Law name _) = name

-- | The body of a 'Law': given five object variables and a supply of named arbitrary arrows,
-- produce an @r k@. A body binds as many of the variables as it uses, e.g. @\\ \@a \@b gen -> ...@,
-- and gives each arrow it asks for the name to print it as.
type LawBody :: [Kind -> Constraint] -> (Kind -> Type) -> Type
type LawBody cs r =
  forall {k} (a :: k) (b :: k) (c :: k) (d :: k) (e :: k) m
   . (Labelled k, All cs k, Monad m, Ob a, Ob b, Ob c, Ob d, Ob e)
  => (forall (x :: k) y. (Ob x, Ob y) => String -> m (x ~> y))
  -> m (r k)

-- * Equations

infix 1 :=:

-- | Two parallel arrows claimed to be equal.
type Equation :: Kind -> Type
data Equation k where
  (:=:) :: forall {k} (a :: k) b. a ~> b -> a ~> b -> Equation k

infix 1 =:=

-- | '(:=:)' as the result of a law body: @l '=:=' r = 'pure' (l ':=:' r)@.
(=:=) :: forall {k} m (a :: k) b. (Applicative m) => a ~> b -> a ~> b -> m (Equation k)
l =:= r = pure (l :=: r)

-- * Inverses

-- | A pair of arrows claimed to be inverse to each other, see 'inverses'.
type Inverses :: Kind -> Type
data Inverses k where
  Inverses :: forall {k} (a :: k) b. a ~> b -> b ~> a -> Inverses k

-- | The body of a law that asks for no arrows: given five object variables, an @r k@.
type PureLawBody :: [Kind -> Constraint] -> (Kind -> Type) -> Type
type PureLawBody cs r =
  forall {k} (a :: k) (b :: k) (c :: k) (d :: k) (e :: k). (Labelled k, All cs k, Ob a, Ob b, Ob c, Ob d, Ob e) => r k

-- | @g . f = id@ and @f . g = id@ for @'Inverses' f g@.
leftInverse, rightInverse :: (CategoryOf k) => Inverses k -> Equation k
leftInverse (Inverses f g) = (g . f :=: id) \\ f
rightInverse (Inverses f g) = (f . g :=: id) \\ f

-- | The two laws saying that a pair of arrows @f@, @g@ are inverse to each other: @g@ is a left
-- and a right inverse of @f@.
inverses :: forall cs. String -> PureLawBody cs Inverses -> [Law cs]
inverses name body = [side " left inverse" leftInverse, side " right inverse" rightInverse]
  where
    side :: String -> (forall k. (CategoryOf k) => Inverses k -> Equation k) -> Law cs
    side suffix eqn = Law (name ++ suffix) \ @a @b @c @d @e _ -> pure (eqn (body @a @b @c @d @e))

-- * Naming arrows

-- | Categories whose arrows can be given a name, for printing laws. Naming leaves the arrow as it
-- is.
type Labelled :: Kind -> Constraint
class (CategoryOf k) => Labelled k where
  -- | @'label' s f@ is @f@, printed as @s@.
  label :: String -> (a :: k) ~> b -> a ~> b
