{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The category __freely generated__ by a quiver @p@ of generator arrows, extended with a chosen
-- list @cs@ of structural classes (terminal object, products, closed structure, ...): an arrow of
-- @'FREE' cs p@ is a formal composite of generators ('Emb') and structure morphisms ('St'). 'fold'
-- interprets such an arrow in any category supporting the same structures, making this the basis
-- for deeply embedded categorical DSLs.
--
-- For a quiver with no structures at all, "Proarrow.Category.Instance.Paths" is the better fit: its
-- objects are the vertices themselves, so they keep the base kind's 'Ob' and can still be taken
-- apart, which an 'IsFreeOb' shape cannot.
--
-- __No equations__: only the category laws hold structurally (composition is a normalized spine);
-- the /structure/ laws do not — @'Proarrow.Limit.BinaryProduct.fst' . (f
-- 'Proarrow.Limit.BinaryProduct.&&&' g)@ and @f@ are different 'Free' values. Equality of 'Free'
-- arrows is semantic: two arrows are equal when every 'fold' identifies them, which is also how
-- the test suite decides it (by interpreting into a concrete category). Don't pattern-match
-- expecting normal forms.
--
-- An object of @'FREE' cs p@ is a /shape/ ('IsFreeOb'): the free category asks nothing of @k@
-- beyond being a category, as a free construction must. Every shape has a denotation
-- @'Lower' f a@ along any functor @f@ out of @k@ into a category with the structures @cs@, and
-- 'withLowerOb' recovers that denotation's 'Ob' when interpreting ('fold').
--
-- The same applies one level up: classes imposing structural /type equalities/ (like
-- 'Proarrow.Category.Monoidal.Cartesian.Cartesian'\'s @tensor = product@) do not hold on the free category
-- as currently encoded -- each class's carrier is fixed, e.g. @**@ is always the formal tensor --
-- and cannot be listed in @cs@. Sometimes re-choosing structure with a kind wrapper recovers the
-- instance: @'Proarrow.Limit.BinaryProduct.PROD' ('FREE' '[HasTerminalObject, HasBinaryProducts] p)@
-- /is/ a free cartesian category.
module Proarrow.Category.Instance.Free where

import Data.Kind (Constraint)
import Prelude (Show (..))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Discrete (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Hom
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , Show2
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

-- | Membership of a structure in the list, with the entailment @'All' cs k => c k@ as a method
-- rather than a quantified superclass: as a given, the quantified form would shadow the ordinary
-- instances for the free category itself and demand @All cs (FREE cs p)@.
type Elem :: (Kind -> Constraint) -> [Kind -> Constraint] -> Constraint
class c `Elem` cs where
  fromAll :: forall k r. (All cs k) => ((c k) => r) -> r

instance {-# OVERLAPPABLE #-} (c `Elem` cs) => c `Elem` (d ': cs) where
  fromAll @k r = fromAll @c @cs @k r
instance c `Elem` (c ': cs) where
  fromAll r = r

-- | Membership of several structures at once: @'[Monoidal, SymMonoidal] \`Elems\` cs@.
type Elems :: [Kind -> Constraint] -> [Kind -> Constraint] -> Constraint
type family ds `Elems` cs where
  '[] `Elems` cs = ()
  (d ': ds) `Elems` cs = (d `Elem` cs, ds `Elems` cs)

-- | The objects of the free category over the quiver @p@ on @k@: the embedded objects of @k@
-- ('EMB') plus one object former per structure in @cs@ (products, exponentials, ...), which live
-- in their structures' modules.
newtype FREE (cs :: [Kind -> Constraint]) (p :: CAT k) = EMB k

-- | Arrows of the free category: a right-associated composition spine ending in 'Nil', with a
-- generator ('Emb') or structure morphism ('St') precomposed onto the rest at each step -- which
-- is what makes the category laws hold definitionally. The fields are linear (@%1@) so that DSL
-- helpers built on 'Free' can offer HOAS-style binders whose bound variable must be used exactly
-- once.
type Free :: CAT (FREE cs p)
data Free a b where
  Nil :: (Ob a) => Free a a
  Emb :: (Ob a, Ob b) => p a b %1 -> Free (i :: FREE cs p) (EMB a) %1 -> Free i (EMB b)
  St
    :: forall {k} {cs} {p :: CAT k} (c :: Kind -> Constraint) (a :: FREE cs p) b i
     . (HasStructure cs p c, Ob a, Ob b)
    => Struct c a b %1 -> Free i a %1 -> Free i b

emb :: (Ob a, Ob b) => p a b %1 -> Free (EMB a :: FREE cs p) (EMB b)
emb p = Emb p Nil

class (Show2 p) => WithShow (a :: FREE c (p :: CAT j))
instance (Show2 p) => WithShow (a :: FREE c (p :: CAT j))

instance (WithShow a) => Show (Free a b) where
  showsPrec _ Nil = P.showString "id"
  showsPrec d (Emb p g) = showPostComp d p g
  showsPrec d (St s g) = showPostComp d s g

showPostComp :: (Show p, WithShow a) => P.Int -> p -> Free a b -> P.ShowS
showPostComp d p Nil = P.showsPrec d p
showPostComp d p g = P.showParen (d P.> 9) (P.showsPrec 10 p . P.showString " . " . P.showsPrec 10 g)

-- | The shape of an object of the free category, by object former -- this /is/ 'Ob' for the free
-- category. It carries the shape's denotation 'Lower' along any functor out of @k@, and how to
-- recover that denotation's 'Ob' from the leaves' ('lowerOb', normally used through
-- 'withLowerOb' and 'withLowerIdOb').
type IsFreeOb :: forall {k} {cs :: [Kind -> Constraint]} {p :: CAT k}. FREE cs p -> Constraint
class IsFreeOb (a :: FREE cs (p :: CAT k)) where
  -- | The denotation of the object along a functor @f@ out of @k@. (The class variable is
  -- re-annotated here so that @k@ is in scope before @f@'s kind mentions it.)
  type Lower (f :: k +-> k') (a :: FREE cs p) :: k'

  lowerOb :: forall k' (f :: k +-> k') r. (Representable f, All cs k') => ((Ob (Lower f a)) => r) -> r

instance (Ob a) => IsFreeOb (EMB a) where
  type Lower f (EMB a) = f % a
  lowerOb @_ @f = withObRep @f @a

-- | @'Ob' ('Lower' f a)@ from the shape of @a@, for interpreting along @f@.
withLowerOb
  :: forall {k} {k'} {cs} {p :: CAT k} (f :: k +-> k') a r
   . (IsFreeOb (a :: FREE cs p), Representable f, All cs k')
  => ((Ob (Lower f a)) => r) -> r
withLowerOb = lowerOb @a @k' @f

-- | 'withLowerOb' along the identity: the 'Ob' of a shape's denotation in @k@ itself, when @k@
-- happens to carry the structures @cs@.
withLowerIdOb
  :: forall {k} {cs} {p :: CAT k} a r
   . (IsFreeOb (a :: FREE cs p), CategoryOf k, All cs k)
  => ((Ob (Lower (Id :: CAT k) a)) => r) -> r
withLowerIdOb = withLowerOb @(Id :: CAT k) @a

class ((Show2 p) => Show2 str) => CanShow (str :: CAT (FREE cs p))
instance ((Show2 p) => Show2 str) => CanShow (str :: CAT (FREE cs p))

class
  (CanShow (Struct c :: CAT (FREE cs p)), c `Elem` cs) =>
  HasStructure cs (p :: CAT k) (c :: Kind -> Constraint)
  where
  data Struct c :: CAT (FREE cs p)
  foldStructure
    :: forall {k'} (f :: k +-> k') (a :: FREE cs p) (b :: FREE cs p)
     . (c k', All cs k', Representable f)
    => (forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y)
    -> Struct c a b
    -> Lower f a ~> Lower f b

-- | Interpret a free arrow along a functor @f@ into any category @k'@ supporting the structures
-- @cs@, given an interpretation of the generators between the images of their objects -- the
-- universal property of the free category. The interpreter is handed @('Ob' x, 'Ob' y)@ explicitly
-- (the evidence bundled on 'Emb'), because a bare quiver @p@ is not a 'Profunctor', so the 'Ob's
-- cannot be recovered from the value.
fold
  :: forall {k} {k'} {p :: CAT k} (cs :: [Kind -> Constraint]) (f :: k +-> k') (a :: FREE cs p) (b :: FREE cs p)
   . (All cs k', Representable f)
  => (forall x y. (Ob x, Ob y) => p x y -> (f % x) ~> (f % y))
  -> a ~> b
  -> Lower f a ~> Lower f b
fold pn = go
  where
    go :: forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y
    go Nil = withLowerOb @f @x id
    go (Emb p g) = pn p . go g
    go (St @c s g) = fromAll @c @cs @k' (foldStructure @_ @_ @_ @_ @f go s) . go g

retract
  :: forall {k} {k'} cs (f :: k +-> k') a b
   . (All cs k', Representable f) => (a :: FREE cs (InitialProfunctor :: CAT k)) ~> b -> Lower f a ~> Lower f b
retract = fold @cs @f (\case {})

-- | Taking the quiver to be the /hom of a category/ @k@ makes @'FREE' cs ('Proarrow.Core.Hom' k)@
-- the free @cs@-structured category over @k@: 'liftFree' embeds the arrows of @k@ as generators,
-- and when @k@ itself already has the structures, 'retractFree' interprets back into @k@ along the
-- identity. These back the free-kind instances of
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
-- profunctor. The base kind must be 'Discrete', since arrows of @k@ other than identities have no
-- counterpart in the free category.
data family Embed :: k +-> FREE ds (p :: CAT k)

instance (Discrete k) => FunctorForRep (Embed :: k +-> FREE ds (p :: CAT k)) where
  type Embed @ a = EMB a
  fmap (f :: x ~> y) = f // withEq f (Nil :: Free (EMB x :: FREE ds p) (EMB x))

-- | Widen a free arrow into a free category over a larger structure list: 'fold' along 'Embed',
-- so each structural object is rebuilt as itself in the larger category (e.g. the terminal object
-- lowers to the target's terminal object) and generators embed as generators. The
-- @'All' cs ('FREE' ds p)@ constraint is exactly the evidence that every structure in @cs@ is
-- also available in @ds@.
widen
  :: forall ds {k} {cs} {p :: CAT k} (a :: FREE cs p) b
   . (All cs (FREE ds p), Discrete k)
  => a ~> b
  -> Lower (Rep (Embed :: k +-> FREE ds p)) a ~> Lower (Rep (Embed :: k +-> FREE ds p)) b
widen = fold @cs @(Rep (Embed :: k +-> FREE ds p)) (\g -> emb g)

-- | The category freely generated from the heteromorphisms of @p@, together with formal
-- structure arrows for each of the classes in @cs@. An object is a shape ('IsFreeOb').
instance CategoryOf (FREE cs p) where
  type (~>) = Free
  type Ob a = IsFreeOb a

instance Promonad (Free :: CAT (FREE cs p)) where
  id = Nil
  Nil . g = g
  f . Nil = f
  Emb p f . g = Emb p (f . g)
  St s f . g = St s (f . g)

instance Profunctor (Free :: CAT (FREE cs p)) where
  dimap = dimapDefault
  r \\ Nil = r
  r \\ Emb _ f = r \\ f
  r \\ St _ f = r \\ f
