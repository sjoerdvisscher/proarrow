{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The category __freely generated__ by a quiver @p@ of generator arrows, extended with a chosen
-- list @cs@ of structural classes (terminal object, products, closed structure, ...): an arrow of
-- @'FREE' cs p@ is a formal composite of generators ('Emb') and structure morphisms ('St'). 'fold'
-- interprets such an arrow in any category supporting the same structures, making this the basis
-- for deeply embedded categorical DSLs.
--
-- __No equations__: only the category laws hold structurally (composition is a normalized spine);
-- the /structure/ laws do not — @'Proarrow.Limit.BinaryProduct.fst' . (f
-- 'Proarrow.Limit.BinaryProduct.&&&' g)@ and @f@ are different 'Free' values. Equality of 'Free'
-- arrows is semantic: two arrows are equal when every 'fold' identifies them, which is also how
-- the test suite decides it (by interpreting into a concrete category). Don't pattern-match
-- expecting normal forms.
--
-- The same applies one level up: classes imposing structural /type equalities/ (like
-- 'Proarrow.Limit.BinaryProduct.Cartesian'\'s @tensor = product@) do not hold on the free category
-- as currently encoded -- each class's carrier is fixed, e.g. @**@ is always the formal tensor --
-- and cannot be listed in @cs@. Sometimes re-choosing structure with a kind wrapper recovers the
-- instance: @'Proarrow.Limit.BinaryProduct.PROD' ('FREE' '[HasTerminalObject, HasBinaryProducts] p)@
-- /is/ a free cartesian category.
module Proarrow.Category.Instance.Free where

import Data.Kind (Constraint)
import Prelude (Eq, Show (..))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Discrete (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Hom
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , dimapDefault
  , (//)
  , type (+->)
  )
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Profunctor.Instance.Identity (Id)
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Representable (Rep, Representable (..), withObRep)

type family All (cs :: [Kind -> Constraint]) (k :: Kind) :: Constraint where
  All '[] k = ()
  All (c ': cs) k = (c k, All cs k)

class ((All cs k) => c k) => FromAll cs c k
instance ((All cs k) => c k) => FromAll cs c k

type Elem :: (Kind -> Constraint) -> [Kind -> Constraint] -> Constraint
class (forall k. FromAll cs c k) => c `Elem` cs
instance {-# OVERLAPPABLE #-} (c `Elem` cs) => c `Elem` (d ': cs)
instance c `Elem` (c ': cs)

newtype FREE (cs :: [Kind -> Constraint]) (p :: CAT j) = EMB j

-- | Arrows of the free category: a right-associated composition spine ending in 'Id', with a
-- generator ('Emb') or structure morphism ('St') precomposed onto the rest at each step -- which
-- is what makes the category laws hold definitionally. The fields are linear (@%1@) so that DSL
-- helpers built on 'Free' can offer HOAS-style binders whose bound variable must be used exactly
-- once.
type Free :: CAT (FREE cs p)
data Free a b where
  Id :: (Ob a) => Free a a
  Emb :: (Ob a, Ob b) => p a b %1 -> Free (i :: FREE cs p) (EMB a) %1 -> Free i (EMB b)
  St
    :: forall {j} {cs} {p :: CAT j} (c :: Kind -> Constraint) (a :: FREE cs p) b i
     . (HasStructure cs p c, Ob a, Ob b)
    => Struct c a b %1 -> Free i a %1 -> Free i b

emb :: (Ob a, Ob b) => p a b %1 -> Free (EMB a :: FREE cs p) (EMB b)
emb p = Emb p Id

-- | Witnesses that every structure class in @cs@ holds for 'FREE cs p' itself. Needed whenever
-- an instance for 'FREE cs p' has to discharge a superclass obligation stated generically over
-- @k@ (e.g. 'Proarrow.Limit.Terminal.HasTerminalObject'\'s own @'Ob' ('Proarrow.Limit.Terminal.TerminalObject' :: k)@) by cashing in @c \`Elem\`
-- cs@'s reflexive implication (@'All' cs k => c k@) at @k = FREE cs p@ — see 'Elem'.
class (All cs (FREE cs p)) => Ok cs (p :: CAT j)

instance (All cs (FREE cs p)) => Ok cs (p :: CAT j)

class (forall x y. Eq (p x y)) => Eq2 p
instance (forall x y. Eq (p x y)) => Eq2 p

class (forall x y. P.Show (p x y)) => Show2 p
instance (forall x y. P.Show (p x y)) => Show2 p

class (Show2 p) => WithShow (a :: FREE c (p :: CAT j))
instance (Show2 p) => WithShow (a :: FREE c (p :: CAT j))

instance (WithShow a) => Show (Free a b) where
  showsPrec _ Id = P.showString "id"
  showsPrec d (Emb p g) = showPostComp d p g
  showsPrec d (St s g) = showPostComp d s g

showPostComp :: (Show p, WithShow a) => P.Int -> p -> Free a b -> P.ShowS
showPostComp d p Id = P.showsPrec d p
showPostComp d p g = P.showParen (d P.> 9) (P.showsPrec 10 p . P.showString " . " . P.showsPrec 10 g)

type IsFreeOb :: forall {j} {cs :: [Kind -> Constraint]} {p :: CAT j}. FREE cs p -> Constraint
class IsFreeOb (a :: FREE cs (p :: CAT j)) where
  type Lower (f :: j +-> k) (a :: FREE cs p) :: k
  withLowerOb :: forall {k} (f :: j +-> k) r. (Representable f, All cs k) => ((Ob (Lower f (a :: FREE cs p))) => r) -> r
instance (Ob a) => IsFreeOb (EMB a) where
  type Lower f (EMB a) = f % a
  withLowerOb @f = withObRep @f @a

class ((Show2 p) => Show2 str) => CanShow (str :: CAT (FREE cs p))
instance ((Show2 p) => Show2 str) => CanShow (str :: CAT (FREE cs p))

class
  (CanShow (Struct c :: CAT (FREE cs p)), c `Elem` cs) =>
  HasStructure cs (p :: CAT j) (c :: Kind -> Constraint)
  where
  data Struct c :: CAT (FREE cs p)
  foldStructure
    :: forall {k} (f :: j +-> k) (a :: FREE cs p) (b :: FREE cs p)
     . (All cs k, Representable f)
    => (forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y)
    -> Struct c a b
    -> Lower f a ~> Lower f b

-- | Interpret a free arrow in any category @k@ supporting the structures @cs@, given an
-- interpretation of the generators -- the universal property of the free category. The
-- interpreter is handed @('Ob' x, 'Ob' y)@ explicitly (the evidence bundled on 'Emb'), because a
-- bare quiver @p@ is not a 'Profunctor', so the 'Ob's cannot be recovered from the value.
fold
  :: forall {j} {k} {p :: CAT j} (cs :: [Kind -> Constraint]) (f :: j +-> k) (a :: FREE cs p) (b :: FREE cs p)
   . (All cs k, Representable f)
  => (forall x y. (Ob x, Ob y) => p x y -> (f % x) ~> (f % y))
  -> a ~> b
  -> Lower f a ~> Lower f b
fold pn = go
  where
    go :: forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y
    go Id = withLowerOb @x @f id
    go (Emb p g) = pn p . go g
    go (St s g) = foldStructure @_ @_ @_ @_ @f go s . go g

retract
  :: forall {j} {k} cs (f :: j +-> k) a b
   . (All cs k, Representable f) => (a :: FREE cs InitialProfunctor) ~> b -> Lower f a ~> Lower f b
retract = fold @cs @f (\case {})

-- | Taking the quiver to be the /hom of a category/ @k@ makes @'FREE' cs ('Proarrow.Core.Hom' k)@
-- the free @cs@-structured category over @k@: 'liftFree' embeds the arrows of @k@ as generators,
-- and when @k@ itself already has the structures, 'retractFree' interprets back into @k@ along the
-- identity profunctor. These back the free-kind instances of
-- 'Proarrow.Profunctor.Free.HasFreeK' (e.g. the free category with a terminal object, or with
-- binary products, over @k@).
liftFree :: forall {k} cs (x :: k) y. (CategoryOf k) => (x ~> y) -> (EMB x :: FREE cs (Hom k)) ~> EMB y
liftFree f = emb f \\ f

retractFree
  :: forall cs {k} (a :: FREE cs (Hom k)) b
   . (CategoryOf k, All cs k)
  => a ~> b
  -> Lower (Id :: CAT k) a ~> Lower (Id :: CAT k) b
retractFree = fold @cs @(Id :: CAT k) (\g -> g)

-- | The object-embedding functor @a |-> 'EMB' a@ of a widening (see 'widen'), as a representable
-- profunctor. The base kind must be 'Discrete', since arrows of @j@ other than identities have no
-- counterpart in the free category.
data family Embed :: j +-> FREE ds (p :: CAT j)

instance (Discrete j) => FunctorForRep (Embed :: j +-> FREE ds (p :: CAT j)) where
  type Embed @ a = EMB a
  fmap (f :: x ~> y) = f // withEq f (Id :: Free (EMB x :: FREE ds p) (EMB x))

-- | Widen a free arrow into a free category over a larger structure list: 'fold' along 'Embed',
-- so each structural object is rebuilt as itself in the larger category (e.g. the terminal object
-- lowers to the target's terminal object) and generators embed as generators. The
-- @'All' cs ('FREE' ds p)@ constraint is exactly the evidence that every structure in @cs@ is
-- also available in @ds@.
widen
  :: forall ds {j} {cs} {p :: CAT j} (a :: FREE cs p) b
   . (All cs (FREE ds p), Discrete j)
  => a ~> b
  -> Lower (Rep (Embed :: j +-> FREE ds p)) a ~> Lower (Rep (Embed :: j +-> FREE ds p)) b
widen = fold @cs @(Rep (Embed :: j +-> FREE ds p)) (\g -> emb g)

-- | The category freely generated from the heteromorphisms of @p@, together with formal
-- structure arrows for each of the classes in @cs@.
instance CategoryOf (FREE cs p) where
  type (~>) = Free
  type Ob a = IsFreeOb a

instance Promonad (Free :: CAT (FREE cs p)) where
  id = Id
  Id . g = g
  f . Id = f
  Emb p f . g = Emb p (f . g)
  St s f . g = St s (f . g)

instance Profunctor (Free :: CAT (FREE cs p)) where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Emb _ f = r \\ f
  r \\ St _ f = r \\ f
