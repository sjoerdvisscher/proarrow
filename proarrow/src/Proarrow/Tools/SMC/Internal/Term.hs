{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": terms and the operations that need no binder. It
-- exports everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Term where

import Data.Kind (Type)
import GHC.TypeNats (Nat, type (+))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (one), associatorInv')
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), obj)
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

-- | Lift an arrow of the promonad to a function on terms: it runs after the term.
{-# INLINE lift #-}
lift
  :: forall {k} (a :: SYN k) b d g (p :: CAT k)
   . (Promonad p) => p (Interp a) (Interp b) -> TermP p d g a -> TermP p d g b
lift f (MkTerm t) = MkTerm (f . t)

-- | Lift a morphism of the category to a function on terms, with 'rmap'. For @p = ('~>')@ this is
-- 'lift'; for other promonads it is how the structure of @k@ acts on terms.
{-# INLINE rmapT #-}
rmapT
  :: forall {k} (a :: SYN k) b d g (p :: CAT k)
   . (Profunctor p) => (Interp a ~> Interp b) -> TermP p d g a -> TermP p d g b
rmapT f (MkTerm t) = MkTerm (rmap f t)

-- | Two terms side by side. A variable both use is copied. With effects, the left term's run
-- first.
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

type TyOf :: forall k. Type -> SYN k
type family TyOf t where
  TyOf (TermP p d g a) = a
