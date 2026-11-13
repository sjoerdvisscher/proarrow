{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": terms and the operations that need no binder. It
-- exports everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Term where

import Data.Kind (Constraint, Type)
import GHC.TypeNats (Nat, type (+))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (one), associatorInv')
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..), arr, obj)
import Proarrow.Monoid (Comonoid (..))
import Prelude (type (~))

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Syntax

infixl 7 **

-- | A term at binding depth @d@ with context @g@ and type @a@, whose computations are arrows of
-- the promonad @p@: an arrow of @p@ from the tensor of the context to @a@. Variables and the
-- structure of contexts are morphisms of the category @k@, which @p@ takes in with 'lmap' and
-- 'rmap'. At @p = ('~>')@ this is 'Term'.
type TermP :: forall {k}. CAT k -> Nat -> Ctx k -> SYN k -> Type
data TermP p d g a where
  MkTerm :: p (Interp (Mul g)) (Interp a) -> TermP p d g a

-- | A term whose computations are the morphisms of the category itself.
type Term :: forall {k}. Nat -> Ctx k -> SYN k -> Type
type Term d g a = TermP (~>) d g a

-- | A term, a constant arrow from the monoidal unit, or a tuple of these.
-- Constants and the empty tuple use no variables; pairs merge their components' contexts.
-- Base-category constants enter a promonad through 'arr'; arrows already in it are kept.
-- Converting a term here keeps its binding depth, unlike tuple construction.
type ToTerm :: forall {k}. CAT k -> Type -> Nat -> Ctx k -> SYN k -> Constraint
class ToTerm p t d g a | p t -> g a where
  -- | Explicit conversion for helpers whose result must be a concrete term.
  toTerm :: t -> TermP p d g a

instance {-# INCOHERENT #-} (t ~ TermP p d g a) => ToTerm p t d g a where
  {-# INLINE toTerm #-}
  toTerm t = t

-- This instance distinguishes terms from the applied-arrow form even before their kinds are known.
instance (TermP q d' g' a' ~ TermP p d g a) => ToTerm p (TermP q d' g' a') d g a where
  {-# INLINE toTerm #-}
  toTerm t = t

-- Native arrows are already in the target promonad. Base-category arrows enter through arr.
-- The native instance is incoherent so an abstract target can still use the pure instance.
type LiftArrow :: forall {k}. CAT k -> CAT k -> Constraint
class LiftArrow p q where
  liftArrow :: q a b -> p a b

instance {-# INCOHERENT #-} LiftArrow p p where
  {-# INLINE liftArrow #-}
  liftArrow f = f

instance {-# OVERLAPPABLE #-} (Promonad p, q ~ Hom k) => LiftArrow (p :: CAT k) q where
  {-# INLINE liftArrow #-}
  liftArrow = arr

instance
  {-# OVERLAPPABLE #-}
  (q x y ~ r Unit b, LiftArrow p r, g ~ '[], a ~ F b)
  => ToTerm p (q x y) d (g :: Ctx k) a
  where
  {-# INLINE toTerm #-}
  toTerm f = MkTerm (liftArrow @p @r f) :: TermP p d '[] (F b)

-- | The empty tuple is the monoidal unit.
instance {-# INCOHERENT #-} (MonoidalProfunctor p, g ~ '[], a ~ I) => ToTerm p () d g a where
  {-# INLINE toTerm #-}
  toTerm () = unit

-- | A pair combines its components as a tensor, merging their contexts.
instance
  {-# INCOHERENT #-}
  ( MonoidalProfunctor p
  , ToTerm p x d g1 a1
  , ToTerm p y d g2 a2
  , Merge g1 g2
  , g ~ Union g1 g2
  , a ~ (a1 :** a2)
  )
  => ToTerm p (x, y) d g a
  where
  {-# INLINE toTerm #-}
  toTerm (x, y) = toTerm @p @x @d @g1 @a1 x ** toTerm @p @y @d @g2 @a2 y

instance {-# INCOHERENT #-} (ToTerm p ((x, y), z) d g a) => ToTerm p (x, y, z) d g a where
  {-# INLINE toTerm #-}
  toTerm (x, y, z) = toTerm @p @((x, y), z) @d @g @a ((x, y), z)

instance {-# INCOHERENT #-} (ToTerm p ((w, x, y), z) d g a) => ToTerm p (w, x, y, z) d g a where
  {-# INLINE toTerm #-}
  toTerm (w, x, y, z) = toTerm @p @((w, x, y), z) @d @g @a ((w, x, y), z)

instance {-# INCOHERENT #-} (ToTerm p ((v, w, x, y), z) d g a) => ToTerm p (v, w, x, y, z) d g a where
  {-# INLINE toTerm #-}
  toTerm (v, w, x, y, z) = toTerm @p @((v, w, x, y), z) @d @g @a ((v, w, x, y), z)

instance {-# INCOHERENT #-} (ToTerm p ((u, v, w, x, y), z) d g a) => ToTerm p (u, v, w, x, y, z) d g a where
  {-# INLINE toTerm #-}
  toTerm (u, v, w, x, y, z) = toTerm @p @((u, v, w, x, y), z) @d @g @a ((u, v, w, x, y), z)

-- | The variable with id @n@: the identity on its type.
{-# INLINE var #-}
var :: forall {k} n (a :: SYN k) d (p :: CAT k). (Promonad p, KnownObj a) => TermP p d '[ '(n, a)] a
var = withSynOb @a (MkTerm (id @p @(Interp a)))

-- | Copy a term whose type is a comonoid: @(x1, x2) <- dup x@. Using a variable twice copies it too,
-- but needs a 'Proarrow.Monoid.CocommutativeComonoid'; 'dup' needs only a 'Comonoid', and its two copies come out
-- in the order of 'comult'.
{-# INLINE dup #-}
dup :: forall {k} (s :: SYN k) d g p. (Profunctor p, Comonoid (Interp s)) => TermP p d g s -> TermP p d g (s :** s)
dup = rmapT @s @(s :** s) comult

-- | Discard a term whose type is a comonoid: @() <- drop t@. A variable that is not used is
-- discarded without it.
{-# INLINE drop #-}
drop :: forall {k} (s :: SYN k) d g p. (Profunctor p, Comonoid (Interp s)) => TermP p d g s -> TermP p d g I
drop = rmapT @s @I counit

-- | Lift an arrow of the promonad to a function on terms, constants or tuples: it runs after the input.
{-# INLINE lift #-}
lift
  :: forall {k} (a :: SYN k) b d g (p :: CAT k) t
   . (Promonad p, ToTerm p t d g a) => p (Interp a) (Interp b) -> t -> TermP p d g b
lift f t = case toTerm @p @t @d @g @a t of
  MkTerm g -> MkTerm (f . g)

-- | Lift a morphism of the category to a function on terms, with 'rmap'. For @p = ('~>')@ this is
-- 'lift'; for other promonads it is how the structure of @k@ acts on terms.
{-# INLINE rmapT #-}
rmapT
  :: forall {k} (a :: SYN k) b d g (p :: CAT k)
   . (Profunctor p) => (Interp a ~> Interp b) -> TermP p d g a -> TermP p d g b
rmapT f (MkTerm t) = MkTerm (rmap f t)

-- | Two concrete terms side by side. A variable both use is copied. With effects, the left
-- term runs first. Use tuples to combine components through 'ToTerm'.
{-# INLINE (**) #-}
(**)
  :: forall {k} d g1 g2 (a :: SYN k) b (p :: CAT k)
   . (MonoidalProfunctor p, Merge g1 g2)
  => TermP p d g1 a -> TermP p d g2 b -> TermP p d (Union g1 g2) (a :** b)
MkTerm f ** MkTerm g = MkTerm (lmap (merge @g1 @g2) (f M.** g))

-- | Two new variables @n@ and @n + 1@, of types @a@ and @b@, for the body of a 'split' whose
-- context is @g'@: the tensor @a ':**' b@, given from the context @g@, next to @r@, what the body
-- uses besides them.
{-# INLINE push2 #-}
push2
  :: forall {k} n (a :: SYN k) b g' r1 r g (p :: CAT k)
   . (Promonad p, MonoidalProfunctor p, KnownObj a, KnownObj b, BindVar (n + 1) b g' r1, BindVar n a r1 r, Merge r g)
  => p (Interp (Mul g)) (Interp a ** Interp b)
  -> p (Interp (Mul (Union r g))) (Interp (Mul g'))
push2 t =
  withCtxOb @r
    ( withSynOb @b
        ( dimap
            (merge @r @g)
            ( bindVar @(n + 1) @b @g' @r1
                . (bindVar @n @a @r1 @r M.** obj @(Interp b))
                . associatorInv' (ctxOb @r) (synOb @a) (synOb @b)
            )
            (id @p @(Interp (Mul r)) M.** t)
        )
    )

-- | Take a tensor apart: the continuation gets a variable for each side.
{-# INLINE split #-}
split
  :: forall {k} d g g' r1 r (a :: SYN k) b c da db (p :: CAT k)
   . (Promonad p, MonoidalProfunctor p, KnownObj a, KnownObj b, BindVar (d + 1) b g' r1, BindVar d a r1 r, Merge r g)
  => TermP p d g (a :** b)
  -> (TermP p da '[ '(d, a)] a -> TermP p db '[ '(d + 1, b)] b -> TermP p (d + 2) g' c)
  -> TermP p d (Union r g) c
split (MkTerm t) k = case k (var @d @a @_ @p) (var @(d + 1) @b @_ @p) of
  MkTerm body -> MkTerm (body . push2 @d @a @b @g' @r1 @r @g @p t)

-- | The unit, which uses no variables.
{-# INLINE unit #-}
unit :: forall {k} d (p :: CAT k). (MonoidalProfunctor p) => TermP p d ('[] :: Ctx k) I
unit = MkTerm one

-- | The same morphism at another type expression for the same object, and at any depth: between
-- @'F' (a '**' b)@ and @'F' a ':**' 'F' b@, say, so that a pattern can take it apart, or between a
-- type and its 'Dn'. The polarity may change, the morphism does not.
{-# INLINE recast #-}
recast :: forall {k} (a :: SYN k) b d d' g p. (Interp a ~ Interp b) => TermP p d g a -> TermP p d' g b
recast (MkTerm f) = MkTerm f

type DepthOf :: Type -> Nat
type family DepthOf t where
  DepthOf (TermP p d g a) = d

type CtxOf :: forall k. Type -> Ctx k
type family CtxOf t where
  CtxOf (TermP p d g a) = g
  CtxOf () = '[]
  CtxOf (x, y) = Union (CtxOf x) (CtxOf y)
  CtxOf (x, y, z) = CtxOf ((x, y), z)
  CtxOf (w, x, y, z) = CtxOf ((w, x, y), z)
  CtxOf (v, w, x, y, z) = CtxOf ((v, w, x, y), z)
  CtxOf (u, v, w, x, y, z) = CtxOf ((u, v, w, x, y), z)
  CtxOf (p (x :: k) (y :: k)) = '[]

type TyOf :: forall k. Type -> SYN k
type family TyOf t where
  TyOf (TermP p d g a) = a
  TyOf () = I
  TyOf (x, y) = TyOf x :** TyOf y
  TyOf (x, y, z) = TyOf ((x, y), z)
  TyOf (w, x, y, z) = TyOf ((w, x, y), z)
  TyOf (v, w, x, y, z) = TyOf ((v, w, x, y), z)
  TyOf (u, v, w, x, y, z) = TyOf ((u, v, w, x, y), z)
  TyOf (p (x :: k) (y :: k)) = F y
