{-# LANGUAGE AllowAmbiguousTypes #-}

-- the identity laws compose with id on purpose
{- HLINT ignore "Redundant id" -}

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
import Prelude (Applicative, Functor, Monad, String, fmap, pure, (++))

import Proarrow.Category.Instance.Free (All)
import Proarrow.Core (CategoryOf (..), Hom, Kind, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Representable (Representable (..), withObRep)

-- * Laws

-- | The laws of the structures @cs@. A class with a new kind of object also needs support in the
-- testing library before its laws can be checked, see "Proarrow.Testing.Laws.Run".
--
-- For example, the laws of a functor on objects @Sq@ with action @sq@ on arrows:
--
-- @
-- instance Laws '[HasSquare] where
--   laws =
--     [ Law "sq identity" \\ \@a _ -> withObSq \@_ \@a (sq (obj \@a) '===' id)
--     , Law "sq composition" \\ \@a \@b \@c mor -> do
--         f <- mor \@a \@b "f"
--         g <- mor \@b \@c "g"
--         sq (g . f) '===' sq g . sq f
--     ]
-- @
type Laws :: [Kind -> Constraint] -> Constraint
class Laws cs where
  -- | The laws, each tested as its own property.
  laws :: [Law cs]

-- | A named law.
type Law :: [Kind -> Constraint] -> Type
data Law cs = Law String (LawBody cs)

-- | The name of a law, used as its test's name.
lawName :: Law cs -> String
lawName (Law name _) = name

-- | The body of a 'Law': given five object variables and a supply of named arbitrary arrows,
-- produce an 'Equation'. A body binds as many of the variables as it uses, e.g. @\\ \@a \@b mor -> ...@,
-- and gives each arrow it asks for the name to print it as.
type LawBody :: [Kind -> Constraint] -> Type
type LawBody cs =
  forall {k} (a :: k) (b :: k) (c :: k) (d :: k) (e :: k) m
   . (Labelled k, All cs k, Monad m, Ob a, Ob b, Ob c, Ob d, Ob e)
  => (forall (x :: k) y. (Ob x, Ob y) => String -> m (x ~> y))
  -> m (Equation k)

-- * Equations

infix 1 :=:

-- | Two parallel elements of a profunctor claimed to be equal, or an equation between arrows of its
-- codomain ('InK') or domain ('InJ').
type ProEquation :: forall {j} {k}. (j +-> k) -> Type
data ProEquation p where
  (:=:) :: forall {j} {k} (p :: j +-> k) a b. p a b -> p a b -> ProEquation p
  InK :: forall {j} {k} (p :: j +-> k). Equation k -> ProEquation p
  InJ :: forall {j} {k} (p :: j +-> k). Equation j -> ProEquation p

-- | Two parallel arrows claimed to be equal: an equation between elements of the hom profunctor.
type Equation :: Kind -> Type
type Equation k = ProEquation (Hom k)

-- | The two sides of an equation between arrows. At the hom profunctor 'InK' and 'InJ' only wrap
-- another equation between arrows of the same category, and are looked through.
withSides :: forall {k} r. Equation k -> (forall (a :: k) b. a ~> b -> a ~> b -> r) -> r
withSides (l :=: r) f = f l r
withSides (InK e) f = withSides e f
withSides (InJ e) f = withSides e f

infix 1 ===

-- | An equation between arrows as the result of a law body: @l '===' r = 'pure' (l ':=:' r)@.
(===) :: forall {k} m (a :: k) b. (Applicative m) => a ~> b -> a ~> b -> m (Equation k)
l === r = pure (l :=: r)

infix 1 =:=

-- | An equation between elements as the result of a profunctor law body:
-- @l '=:=' r = 'pure' (l ':=:' r)@.
(=:=) :: forall {j} {k} m (p :: j +-> k) a b. (Applicative m) => p a b -> p a b -> m (ProEquation p)
l =:= r = pure (l :=: r)

-- | An equation between arrows of the codomain, as the result of a profunctor law body.
inK :: forall {j} {k} m (p :: j +-> k). (Functor m) => m (Equation k) -> m (ProEquation p)
inK = fmap InK

-- | An equation between arrows of the domain, as the result of a profunctor law body.
inJ :: forall {j} {k} m (p :: j +-> k). (Functor m) => m (Equation j) -> m (ProEquation p)
inJ = fmap InJ

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

-- * Bijections

-- | Two maps between hom-sets claimed to be inverse to each other, see 'bijection', with how to
-- ask for an arrow of either hom-set.
type Bijection :: (Type -> Type) -> Kind -> Type
data Bijection m k where
  Bijection
    :: forall {k} m (a :: k) (b :: k) (c :: k) (d :: k)
     . m (a ~> b) -> m (c ~> d) -> (a ~> b -> c ~> d) -> (c ~> d -> a ~> b) -> Bijection m k

-- | The body of a 'bijection': given five object variables and a supply of named arbitrary arrows,
-- the two maps, with how to ask for an arrow of each hom-set.
type BijectionBody :: [Kind -> Constraint] -> Type
type BijectionBody cs =
  forall {k} (a :: k) (b :: k) (c :: k) (d :: k) (e :: k) m
   . (Labelled k, All cs k, Monad m, Ob a, Ob b, Ob c, Ob d, Ob e)
  => (forall (x :: k) y. (Ob x, Ob y) => String -> m (x ~> y))
  -> Bijection m k

-- | The two laws saying that maps @to@ and @from@ between hom-sets are inverse to each other:
-- @from (to f) = f@ and @to (from g) = g@. Each asks only for the arrow it needs, so an empty
-- hom-set on the other side discards nothing.
bijection :: forall cs. String -> BijectionBody cs -> [Law cs]
bijection name body =
  [ Law (name ++ " left inverse") \ @a @b @c @d @e mor -> case body @a @b @c @d @e mor of
      Bijection askF _ to from -> do
        f <- askF
        f === from (to f)
  , Law (name ++ " right inverse") \ @a @b @c @d @e mor -> case body @a @b @c @d @e mor of
      Bijection _ askG to from -> do
        g <- askG
        g === to (from g)
  ]

-- * The laws of a category

-- | 'id' is a unit for composition, which is associative.
instance Laws '[CategoryOf] where
  laws =
    [ Law "left identity" \ @a @b mor -> do
        f <- mor @a @b "f"
        f === id . f
    , Law "right identity" \ @a @b mor -> do
        f <- mor @a @b "f"
        f === f . id
    , Law "associativity" \ @a @b @c @d mor -> do
        f <- mor @a @b "f"
        g <- mor @b @c "g"
        h <- mor @c @d "h"
        h . (g . f) === (h . g) . f
    ]

-- * Profunctor laws

-- | The laws of the profunctor class @c@, for any profunctor @p@ with @c p@. The instances for
-- classes that "Proarrow.Category.Instance.Free" depends on live here.
type ProLaws :: forall {j} {k}. ((j +-> k) -> Constraint) -> Constraint
class ProLaws c where
  -- | The laws, each tested as its own property.
  proLaws :: [ProLaw c]

-- | A named profunctor law, about one element of the profunctor ('ProLaw') or three ('ProLaw3').
type ProLaw :: forall {j} {k}. ((j +-> k) -> Constraint) -> Type
data ProLaw c = ProLaw String (ProLawBody c) | ProLaw3 String (ProLawBody3 c)

-- | The name of a profunctor law, used as its test's name.
proLawName :: ProLaw c -> String
proLawName (ProLaw name _) = name
proLawName (ProLaw3 name _) = name

-- | The body of a 'ProLaw': given a profunctor @p :: j '+->' k@, six object variables alternating
-- between @k@ and @j@, an element @p :: p a b@ between the first two, and a supply of named
-- arbitrary arrows for each of @k@ and @j@, produce a 'ProEquation'. The element picks its
-- endpoints, so that a test can draw it where @p@ has elements, and a test draws the other
-- variables so that there are arrows @e '~>' c '~>' a@ and @b '~>' d '~>' f@. A body binds as many
-- of the variables as it uses, e.g. @\\ \@_ \@a \@b p morK _ -> ...@.
type ProLawBody :: forall {j} {k}. ((j +-> k) -> Constraint) -> Type
type ProLawBody (cl :: (j +-> k) -> Constraint) =
  forall (p :: j +-> k) (a :: k) (b :: j) (c :: k) (d :: j) (e :: k) (f :: j) m
   . (cl p, Labelled j, Labelled k, Monad m, Ob a, Ob b, Ob c, Ob d, Ob e, Ob f)
  => p a b
  -> (forall (x :: k) y. (Ob x, Ob y) => String -> m (x ~> y))
  -> (forall (x :: j) y. (Ob x, Ob y) => String -> m (x ~> y))
  -> m (ProEquation p)

-- | The body of a 'ProLaw3': a 'ProLawBody' with three elements @p :: p a b@, @p' :: p c d@ and
-- @p'' :: p e f@, which pick all six object variables. A law that needs arbitrary objects uses the
-- endpoints of an element it does not otherwise use.
type ProLawBody3 :: forall {j} {k}. ((j +-> k) -> Constraint) -> Type
type ProLawBody3 (cl :: (j +-> k) -> Constraint) =
  forall (p :: j +-> k) (a :: k) (b :: j) (c :: k) (d :: j) (e :: k) (f :: j) m
   . (cl p, Labelled j, Labelled k, Monad m, Ob a, Ob b, Ob c, Ob d, Ob e, Ob f)
  => p a b
  -> p c d
  -> p e f
  -> (forall (x :: k) y. (Ob x, Ob y) => String -> m (x ~> y))
  -> (forall (x :: j) y. (Ob x, Ob y) => String -> m (x ~> y))
  -> m (ProEquation p)

-- | 'dimap' preserves identities and composition, and 'lmap' and 'rmap' are its two halves.
instance ProLaws Profunctor where
  proLaws =
    [ ProLaw "dimap identity" \p _ _ -> p =:= dimap id id p
    , ProLaw "dimap composition" \ @_ @a @b @c @d @e @f p morK morJ -> do
        g <- morK @c @a "g"
        h <- morJ @b @d "h"
        g' <- morK @e @c "g'"
        h' <- morJ @d @f "h'"
        dimap (g . g') (h' . h) p =:= dimap g' h' (dimap g h p)
    , ProLaw "lmap" \ @_ @a @_ @c p morK _ -> do
        g <- morK @c @a "g"
        lmap g p =:= dimap g id p
    , ProLaw "rmap" \ @_ @_ @b @_ @d p _ morJ -> do
        h <- morJ @b @d "h"
        rmap h p =:= dimap id h p
    ]

-- | 'index' and 'tabulate' are inverse and natural, and 'repUniv' is @'tabulate' 'id'@.
instance ProLaws Representable where
  proLaws =
    [ ProLaw "tabulate . index" \p _ _ -> p =:= tabulate (index p)
    , ProLaw "index . tabulate" \ @p @a @b _ morK _ -> withObRep @p @b do
        g <- morK @a @(p % b) "g"
        inK (g === index (tabulate @p @b g))
    , ProLaw "index naturality" \ @p @a @b @c @d p morK morJ -> do
        g <- morK @c @a "g"
        h <- morJ @b @d "h"
        inK (index (dimap g h p) === repMap @p h . index p . g)
    , ProLaw "repUniv" \ @p @_ @b _ _ _ -> withObRep @p @b (repUniv @p @b =:= tabulate id)
    ]

-- * Naming arrows

-- | Categories whose arrows can be given a name, for printing laws. Naming leaves the arrow as it
-- is.
type Labelled :: Kind -> Constraint
class (CategoryOf k) => Labelled k where
  -- | @'label' s f@ is @f@, printed as @s@.
  label :: String -> (a :: k) ~> b -> a ~> b
