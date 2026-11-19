{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The category __freely generated__ by a quiver @p@ of generator arrows, extended with a chosen
-- list @cs@ of structural classes (terminal object, products, closed structure, ...): an arrow of
-- @'FREE' cs p@ is a formal composite of generators ('Emb') and structure morphisms ('St'). 'fold'
-- interprets such an arrow in any category supporting the same structures, making this the basis
-- for deeply embedded categorical DSLs.
--
-- For a quiver with no structures, "Proarrow.Category.Instance.Paths" fits better: its objects are
-- the vertices themselves, which keep the base kind's 'Ob' and can be taken apart.
--
-- __No equations__: only the category laws hold structurally (composition is a normalized spine).
-- For example @'Proarrow.Limit.BinaryProduct.fst' . (f 'Proarrow.Limit.BinaryProduct.&&&' g)@ and
-- @f@ are different 'Free' values. Two arrows are equal when every 'fold' identifies them, so
-- decide equality by interpreting into a concrete category, not by pattern matching.
--
-- An object is a /shape/ ('IsFreeOb'), asking nothing of @k@ beyond being a category. Its
-- denotation along a functor @f@ out of @k@ is @'Lower' f a@, and 'withLowerOb' recovers that
-- denotation's 'Ob' in 'fold'.
--
-- Tensor and product remain distinct formal object shapes. Structures such as
-- 'Proarrow.Category.Monoidal.Cartesian.Cartesian' connect them with explicit
-- coherence arrows, whose interpretations may be identities.
module Proarrow.Category.Instance.Free where

import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable)
import Prelude (Applicative, Bool, Show (..), type (~))
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
  , (\\)
  , type (+->)
  )
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Profunctor.Instance.Identity (Id)
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Representable (Rep, Representable (..), withObRep)

type family All (cs :: [Kind -> Constraint]) (k :: Kind) :: Constraint where
  All '[] k = ()
  All (c ': cs) k = (c k, All cs k)

-- | Membership of a structure in the list, witnessed by its position.
type Elem :: (Kind -> Constraint) -> [Kind -> Constraint] -> Constraint
class c `Elem` cs where
  elemEvidence :: ElemEvidence c cs

-- | The position selected by an 'Elem' instance, for looking up opt-in support.
type ElemEvidence :: a -> [a] -> Type
data ElemEvidence c cs where
  ElemHere :: ElemEvidence c (c ': cs)
  ElemThere :: ElemEvidence c cs -> ElemEvidence c (d ': cs)

instance {-# OVERLAPPABLE #-} (c `Elem` cs) => c `Elem` (d ': cs) where
  elemEvidence = ElemThere (elemEvidence @c @cs)
instance c `Elem` (c ': cs) where
  elemEvidence = ElemHere

-- | Select a structure constraint from 'All' using its membership evidence.
-- The entailment is a continuation rather than a quantified superclass of 'Elem':
-- as a given, the quantified form would shadow ordinary free-category instances.
fromAll :: forall c cs k r. (c `Elem` cs, All cs k) => ((c k) => r) -> r
fromAll = go (elemEvidence @c @cs)
  where
    go :: forall ds. (All ds k) => ElemEvidence c ds -> ((c k) => r) -> r
    go ElemHere r = r
    go (ElemThere rest) r = go rest r

-- | Membership of several structures at once: @'[Monoidal, SymMonoidal] \`Elems\` cs@.
type Elems :: [Kind -> Constraint] -> [Kind -> Constraint] -> Constraint
type family ds `Elems` cs where
  '[] `Elems` cs = ()
  (d ': ds) `Elems` cs = (d `Elem` cs, ds `Elems` cs)

-- | The objects of the free category over the quiver @p@ on @k@: the embedded objects of @k@
-- ('EMB') plus one object former per structure in @cs@ (products, exponentials, ...), which live
-- in their structures' modules.
type data FREE (cs :: [Kind -> Constraint]) (p :: CAT k) = EMB k

-- | Arrows of the free category: a right-associated composition spine ending in 'Nil', with a
-- generator ('Emb') or structure morphism ('St') precomposed onto the rest at each step, so
-- the category laws hold definitionally. The fields are linear (@%1@) so that DSL
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

-- | The shape of an object of the free category, by object former. This is 'Ob' for the free
-- category. It carries the shape's denotation 'Lower' along any functor out of @k@, and how to
-- recover that denotation's 'Ob' from the leaves' ('lowerOb', normally used through
-- 'withLowerOb' and 'withLowerIdOb'). Lowering along 'Embed' preserves the
-- object itself, as recorded by the superclass equality.
type IsFreeOb :: forall {k} {cs :: [Kind -> Constraint]} {p :: CAT k}. FREE cs p -> Constraint
class (Lower (Rep (Embed :: k +-> FREE cs p)) a ~ a) => IsFreeOb (a :: FREE cs (p :: CAT k)) where
  -- | The denotation of the object along a functor @f@ out of @k@. (The class variable is
  -- re-annotated here so that @k@ is in scope before @f@'s kind mentions it.)
  type Lower (f :: k +-> k') (a :: FREE cs p) :: k'

  lowerOb :: forall k' (f :: k +-> k') r. (Representable f, All cs k') => ((Ob (Lower f a)) => r) -> r

  -- | Recover runtime type evidence when base objecthood provides it.
  -- The syntax parameters need runtime type evidence only for this operation;
  -- ordinary free objects and arrows impose no such requirement.
  withTypeableFreeOb
    :: (Typeable k, Typeable cs, Typeable p, forall (x :: k). (Ob x) => Typeable x)
    => ((Typeable a) => r)
    -> r

instance (Ob a) => IsFreeOb (EMB a) where
  type Lower f (EMB a) = f % a
  lowerOb @_ @f = withObRep @f @a
  withTypeableFreeOb r = r

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

  -- | Interpret an operation, visiting each immediate child once in order.
  -- Folding along @Rep (Embed :: k +-> FREE cs p)@ interprets it back into
  -- its own free category, returning a 'Free' arrow. This requires a discrete
  -- base and @All cs (FREE cs p)@; 'fromAll' supplies the selected @c (FREE cs p)@.
  -- Match child arrows with 'Proarrow.Object.Objs' to recover self-lowering
  -- equalities when returning rewritten children.
  foldStructure
    :: forall {k'} (f :: k +-> k') m (a :: FREE cs p) b
     . (Applicative m, c k', All cs k', Representable f)
    => (forall (x :: FREE cs p) y. x ~> y -> m (Lower f x ~> Lower f y))
    -> Struct c a b
    -> m (Lower f a ~> Lower f b)

  -- | Compare outer operations independently of children and object choices.
  -- Fixed payloads participate in this equivalence relation; rebuilding preserves it.
  sameStructure :: Struct c (a :: FREE cs p) b -> Struct c (x :: FREE ds q) y -> Bool

-- | One immediate child, retaining its endpoint types.
type StructureChild :: forall {k}. [Kind -> Constraint] -> CAT k -> Type
data StructureChild cs p where
  StructureChild :: (a :: FREE cs p) ~> b -> StructureChild cs p

-- | Enumerate immediate children in the order used by 'foldStructure'.
structureChildren
  :: forall {k} {cs} {p :: CAT k} c (a :: FREE cs p) b
   . (HasStructure cs p c, Discrete k, All cs (FREE cs p))
  => Struct c a b -> [StructureChild cs p]
structureChildren s =
  fromAll @c @cs @(FREE cs p) P.$
    getConst (foldStructure @_ @_ @_ @_ @(Rep (Embed :: k +-> FREE cs p)) (\child -> Const [StructureChild child]) s)

-- | Compare membership positions, retaining equality of the selected structures.
sameElem :: ElemEvidence c cs -> ElemEvidence d cs -> P.Maybe (c :~: d)
sameElem ElemHere ElemHere = P.Just Refl
sameElem (ElemThere c) (ElemThere d) = sameElem c d
sameElem _ _ = P.Nothing

-- | Interpret a free arrow along a functor @f@ into any category @k'@ supporting the structures
-- @cs@, given an interpretation of the generators between the images of their objects. This is
-- the universal property of the free category. The interpreter is handed @('Ob' x, 'Ob' y)@ explicitly
-- (the evidence bundled on 'Emb'), because a bare quiver @p@ is not a 'Profunctor', so the 'Ob's
-- cannot be recovered from the value.
fold
  :: forall {k} {k'} {p :: CAT k} (cs :: [Kind -> Constraint]) (f :: k +-> k') (a :: FREE cs p) (b :: FREE cs p)
   . (All cs k', Representable f)
  => (forall x y. (Ob x, Ob y) => p x y -> (f % x) ~> (f % y))
  -> a ~> b
  -> Lower f a ~> Lower f b
fold pn term = runIdentity (foldA @cs @f (\p -> Identity (pn p)) term)

-- | 'fold' with applicative effects. Composition visits the input side first,
-- and structural children are visited in the order specified by 'foldStructure'.
foldA
  :: forall {k} {k'} {p :: CAT k} (cs :: [Kind -> Constraint]) (f :: k +-> k') m (a :: FREE cs p) b
   . (Applicative m, All cs k', Representable f)
  => (forall x y. (Ob x, Ob y) => p x y -> m ((f % x) ~> (f % y)))
  -> a ~> b
  -> m (Lower f a ~> Lower f b)
foldA pn = go
  where
    go :: forall (x :: FREE cs p) y. x ~> y -> m (Lower f x ~> Lower f y)
    go Nil = P.pure (withLowerOb @f @x id)
    go (Emb p g) = (\g' p' -> p' . g') P.<$> go g P.<*> pn p
    go (St @c s g) =
      (\g' s' -> s' . g') P.<$> go g P.<*> fromAll @c @cs @k' (foldStructure @_ @_ @_ @_ @f go s)

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
-- @'All' cs ('FREE' ds p)@ constraint is the evidence that every structure in @cs@ is
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
