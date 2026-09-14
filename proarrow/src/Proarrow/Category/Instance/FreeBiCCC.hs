{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The free bicartesian closed category on a generating profunctor @p@.
--
-- Unlike "Proarrow.Category.Instance.Free" (which is generic over an arbitrary /list/ of
-- structures), this is hardcoded to exactly the BiCCC signature. The point of the dedicated
-- encoding is simplicity: a closed object grammar whose shapes are the objects, every
-- structural morphism a 'Step' in a composition spine ('Term'), and the type equality @tensor = product@ stated
-- directly (its 'Proarrow.Category.Monoidal.Monoidal' instance sets @a ** b = a && b@) -- which is
-- what makes it a comfortable foundation for tools like "Proarrow.Tools.CCC". It is genuinely
-- free: the base @k@ need only be a category; @BiCCC@ is asked of the /target/ of 'interp'.
module Proarrow.Category.Instance.FreeBiCCC
  ( FBC (..)
  , Term (..)
  , Step (..)
  , step
  , emb
  , Lower
  , interp
  , KnownFBCOb (fbcCase)
  , withLowerOb
  , withLowerIdOb
  , fbcOb
  ) where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Cartesian (BiCCC)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, type (+->))
import Proarrow.Limit.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , diag
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  )
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..))
import Proarrow.Profunctor.Instance.Identity (Id)
import Proarrow.Profunctor.Representable (Representable (..), withObRep, type (%))

-- | Object expressions of the free BiCCC on generators @p@: base objects (@OBJ@, carrying an
-- actual object of @k@ — the category @p@'s generating morphisms are themselves between),
-- plus terminal\/initial objects and products, coproducts and exponentials of
-- sub-expressions.
type data FBC (p :: k +-> k)
  = OBJ k
  | UNIT
  | PROD (FBC p) (FBC p)
  | ZERO
  | SUM (FBC p) (FBC p)
  | EXPO (FBC p) (FBC p)

-- | Interpret an object expression along a functor @f@ out of the base category: base objects go
-- through @f@ and the formers are rebuilt in the target. This is the object part of 'interp', the
-- universal property of the free BiCCC; @Lower ('Id' :: 'CAT' k)@ is an object's denotation in @k@
-- itself, and is what 'Ob' carries (see the 'CategoryOf' instance).
type family Lower (f :: k +-> k') (a :: FBC (p :: k +-> k)) :: k' where
  Lower f (OBJ x) = f % x
  Lower f UNIT = TerminalObject
  Lower f (PROD a b) = Lower f a && Lower f b
  Lower f ZERO = InitialObject
  Lower f (SUM a b) = Lower f a || Lower f b
  Lower f (EXPO a b) = Lower f a ~~> Lower f b

-- | One operation of the free BiCCC, between the objects it acts on: a generator ('Emb') or a
-- structural morphism, with the sub-terms of 'Pair', 'Case' and 'Curry' kept relative to the
-- object the step acts on. @p@ (and with it the base category @k@) is carried purely by the kind
-- of @a@\/@b@ (@FBC p@), the same way "Proarrow.Category.Instance.Free"'s @Struct@ carries its
-- structure list.
type Step :: CAT (FBC p)
data Step a b where
  Emb :: (Ob x, Ob y) => p x y -> Step (OBJ x :: FBC p) (OBJ y)
  Terminate :: (Ob a) => Step a UNIT
  Absurd :: (Ob a) => Step ZERO a
  Fst :: (Ob a, Ob b) => Step (PROD a b) a
  Snd :: (Ob a, Ob b) => Step (PROD a b) b
  Pair :: Term c a -> Term c b -> Step c (PROD a b)
  Inl :: (Ob a, Ob b) => Step a (SUM a b)
  Inr :: (Ob a, Ob b) => Step b (SUM a b)
  Case :: Term a c -> Term b c -> Step (SUM a b) c
  Curry :: (Ob a, Ob b) => Term (PROD a b) c -> Step a (EXPO b c)
  Apply :: (Ob a, Ob b) => Step (PROD (EXPO a b) a) b

-- | A term of the free BiCCC: a right-associated composition spine of 'Step's ending in 'Nil',
-- exactly the shape of "Proarrow.Category.Instance.Free"'s @Free@, so the category laws hold
-- definitionally. No other equations: e.g. @fst . (f &&& g)@ and @f@ are different 'Term's that
-- interpret to the same morphism, and equality is decided by 'interp'.
type Term :: CAT (FBC p)
data Term a b where
  Nil :: (Ob a) => Term a a
  Cons :: (Ob a, Ob b) => Step a b -> Term i a -> Term i b

-- | A single step as a term.
step :: forall {k} {p :: k +-> k} (a :: FBC p) b. (Ob a, Ob b) => Step a b -> Term a b
step s = Cons s Nil

-- | A generator as a term.
emb :: forall {k} {p :: k +-> k} (x :: k) y. (Ob x, Ob y) => p x y -> Term (OBJ x :: FBC p) (OBJ y)
emb g = step (Emb g)

instance forall k (p :: k +-> k). Profunctor (Term :: CAT (FBC p)) where
  dimap = dimapDefault
  r \\ Nil = r
  r \\ Cons _ g = r \\ g

instance forall k (p :: k +-> k). Promonad (Term :: CAT (FBC p)) where
  id = Nil
  Nil . g = g
  Cons s f . g = Cons s (f . g)

-- | The bicartesian closed category freely generated over the objects of @k@ and the generators
-- @p@: arrows are 'Term's, interpreted into any BiCCC by 'interp'. An object is a shape.
instance forall k (p :: k +-> k). CategoryOf (FBC p) where
  type (~>) = Term
  type Ob (a :: FBC (p :: k +-> k)) = KnownFBCOb a

-- | Witnesses that an object expression is well-formed by case analysis on its shape.
type KnownFBCOb :: forall {k} {p :: k +-> k}. FBC p -> Constraint
class KnownFBCOb (a :: FBC (p :: k +-> k)) where
  fbcCase
    :: (forall x. (a ~ OBJ x, Ob (x :: k)) => r)
    -> ((a ~ UNIT) => r)
    -> (forall x y. (a ~ PROD x y, Ob x, Ob y) => r)
    -> ((a ~ ZERO) => r)
    -> (forall x y. (a ~ SUM x y, Ob x, Ob y) => r)
    -> (forall x y. (a ~ EXPO x y, Ob x, Ob y) => r)
    -> r

instance (Ob x) => KnownFBCOb (OBJ x :: FBC p) where
  fbcCase o _ _ _ _ _ = o

instance forall k (p :: k +-> k). KnownFBCOb (UNIT :: FBC p) where
  fbcCase _ u _ _ _ _ = u

instance forall k (p :: k +-> k). KnownFBCOb (ZERO :: FBC p) where
  fbcCase _ _ _ z _ _ = z

instance forall k (p :: k +-> k) a b. (KnownFBCOb (a :: FBC p), KnownFBCOb b) => KnownFBCOb (PROD a b) where
  fbcCase _ _ prod _ _ _ = prod

instance forall k (p :: k +-> k) a b. (KnownFBCOb (a :: FBC p), KnownFBCOb b) => KnownFBCOb (SUM a b) where
  fbcCase _ _ _ _ sm _ = sm

instance forall k (p :: k +-> k) a b. (KnownFBCOb (a :: FBC p), KnownFBCOb b) => KnownFBCOb (EXPO a b) where
  fbcCase _ _ _ _ _ ex = ex

-- | Recover 'Ob' of the shape interpreted along @f@ into a BiCCC @k'@ (needed to call the
-- target's own 'withObProd'\/'withObCoprod'\/'withObExp'), by case analysis via 'fbcCase'. This is
-- where @BiCCC@ enters: the free category itself asks nothing of @k@.
withLowerOb
  :: forall {k} {k'} {p :: k +-> k} (f :: k +-> k') a r
   . (BiCCC k', KnownFBCOb (a :: FBC p), Representable f)
  => ((Ob (Lower f a)) => r) -> r
withLowerOb r =
  fbcCase @a
    (\ @x -> withObRep @f @x r)
    r
    (\ @x @y -> withLowerOb @f @x (withLowerOb @f @y (withObProd @k' @(Lower f x) @(Lower f y) r)))
    r
    (\ @x @y -> withLowerOb @f @x (withLowerOb @f @y (withObCoprod @k' @(Lower f x) @(Lower f y) r)))
    (\ @x @y -> withLowerOb @f @x (withLowerOb @f @y (withObExp @k' @(Lower f x) @(Lower f y) r)))

-- | 'withLowerOb' at the identity: the 'Ob' of a shape's denotation in @k@ itself, when @k@ is a
-- BiCCC.
withLowerIdOb
  :: forall {k} {p :: k +-> k} a r. (BiCCC k, KnownFBCOb (a :: FBC p)) => ((Ob (Lower (Id :: CAT k) a)) => r) -> r
withLowerIdOb = withLowerOb @(Id :: CAT k) @a

-- | The identity morphism on a shape. A shape /is/ an object ('CategoryOf' above), so this is
-- 'Id'; it is kept as the name the DSL in "Proarrow.Tools.CCC" reaches for.
fbcOb :: forall {k} {p :: k +-> k} a. (KnownFBCOb (a :: FBC p)) => Term a a
fbcOb = Nil

instance forall k (p :: k +-> k). HasTerminalObject (FBC p) where
  type TerminalObject = UNIT
  terminate = step Terminate
instance forall k (p :: k +-> k). HasInitialObject (FBC p) where
  type InitialObject = ZERO
  initiate = step Absurd

instance forall k (p :: k +-> k). HasBinaryProducts (FBC p) where
  type a && b = PROD a b
  withObProd r = r
  fst = step Fst
  snd = step Snd
  f &&& g = step (Pair f g) \\ f \\ g

instance forall k (p :: k +-> k). HasBinaryCoproducts (FBC p) where
  type a || b = SUM a b
  withObCoprod r = r
  lft = step Inl
  rgt = step Inr
  f ||| g = step (Case f g) \\ f \\ g

instance forall k (p :: k +-> k). MonoidalProfunctor (Term :: CAT (FBC p)) where
  one = id
  (**) = (***)

-- | The free bicartesian closed category is cartesian, so every object is a (natural) comonoid:
-- the diagonal and the terminal map.
instance forall k (p :: k +-> k) (a :: FBC p). (Ob a) => Comonoid a where
  counit = terminate
  comult = diag

instance forall k (p :: k +-> k) (a :: FBC p). (Ob a) => CocommutativeComonoid a
instance forall k (p :: k +-> k). CopyDiscard (FBC p)

instance forall k (p :: k +-> k). Monoidal (FBC p) where
  type a ** b = a && b
  type Unit = TerminalObject
  withOb2 @a @b = withObProd @_ @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @a @b @c = associatorProd @a @b @c
  associatorInv @a @b @c = associatorProdInv @a @b @c
instance forall k (p :: k +-> k). SymMonoidal (FBC p) where
  swap @a @b = swapProd @a @b

instance forall k (p :: k +-> k). Closed (FBC p) where
  type a ~~> b = EXPO a b
  withObExp r = r
  curry f = step (Curry f) \\ f
  apply = step Apply

-- | Interpret a 'Term' along a functor @f@ into any BiCCC @k'@, given an interpretation of the
-- generators between the images of their objects -- the universal property of the free BiCCC.
-- At @f = 'Id'@ this evaluates the term in the base category @k@ itself. This is the one place the
-- meaning of a 'Term' is pinned down; everything else (including equality) is defined in terms
-- of it.
interp
  :: forall {k} {k'} (p :: k +-> k) (f :: k +-> k') src tgt
   . (BiCCC k', Representable f)
  => (forall x y. (Ob x, Ob y) => p x y -> f % x ~> f % y)
  -> Term (src :: FBC p) tgt
  -> Lower f src ~> Lower f tgt
interp gn = go
  where
    go :: forall (x :: FBC p) y. Term x y -> Lower f x ~> Lower f y
    go (Nil @a) = withLowerOb @f @a id
    go (Cons s g) = interpStep @p @f gn s . go g

-- | Interpret one 'Step'; the sub-terms of 'Pair', 'Case' and 'Curry' go through 'interp'.
interpStep
  :: forall {k} {k'} (p :: k +-> k) (f :: k +-> k') s t
   . (BiCCC k', Representable f)
  => (forall x y. (Ob x, Ob y) => p x y -> f % x ~> f % y)
  -> Step (s :: FBC p) t
  -> Lower f s ~> Lower f t
interpStep gn (Emb g) = gn g
interpStep _ (Terminate @a) = withLowerOb @f @a (terminate @k' @(Lower f a))
interpStep _ (Absurd @a) = withLowerOb @f @a (initiate @k' @(Lower f a))
interpStep _ (Fst @a @b) = withLowerOb @f @a (withLowerOb @f @b (fst @k' @(Lower f a) @(Lower f b)))
interpStep _ (Snd @a @b) = withLowerOb @f @a (withLowerOb @f @b (snd @k' @(Lower f a) @(Lower f b)))
interpStep gn (Pair l r) = interp @p @f gn l &&& interp @p @f gn r
interpStep _ (Inl @a @b) = withLowerOb @f @a (withLowerOb @f @b (lft @k' @(Lower f a) @(Lower f b)))
interpStep _ (Inr @a @b) = withLowerOb @f @a (withLowerOb @f @b (rgt @k' @(Lower f a) @(Lower f b)))
interpStep gn (Case l r) = interp @p @f gn l ||| interp @p @f gn r
interpStep gn (Curry @a @b @c h) =
  withLowerOb @f @a (withLowerOb @f @b (curry @k' @(Lower f a) @(Lower f b) @(Lower f c) (interp @p @f gn h)))
interpStep _ (Apply @a @b) = withLowerOb @f @a (withLowerOb @f @b (apply @k' @(Lower f a) @(Lower f b)))
