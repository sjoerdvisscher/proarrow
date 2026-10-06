{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": terms and the operations that need no binder. It
-- exports everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Term where

import Data.Kind (Type)
import GHC.TypeNats (Nat, type (+))
import Proarrow.Category.Monoidal (Monoidal (..), associatorInv')
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Monoid (Comonoid (..))
import Prelude (type (~))

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Syntax

infixl 7 **

-- | A term at binding depth @d@ with context @g@ and type @a@: a morphism from the tensor of
-- the context to @a@.
type Term :: forall {k}. Nat -> Ctx k -> SYN k -> Type
data Term d g a where
  MkTerm :: (Interp (Mul g) ~> Interp a) -> Term d g a

-- | The variable with id @n@: the identity on its type.
{-# INLINE var #-}
var :: forall {k} n (a :: SYN k) d. (CategoryOf k, KnownObj a) => Term d '[ '(n, a)] a
var = withSynOb @a (MkTerm (obj @(Interp a)))

-- | Copy a term whose type is a comonoid: @(x1, x2) <- dup x@. Using a variable twice copies it too,
-- but needs a 'Proarrow.Monoid.CocommutativeComonoid'; 'dup' needs only a 'Comonoid', and its two copies come out
-- in the order of 'comult'.
{-# INLINE dup #-}
dup :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s -> Term d g (s :** s)
dup = lift @s @(s :** s) comult

-- | Discard a term whose type is a comonoid: @() <- drop t@. A variable that is not used is
-- discarded without it.
{-# INLINE drop #-}
drop :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s -> Term d g I
drop = lift @s @I counit

-- | Lift a morphism of the target category to a function on terms.
{-# INLINE lift #-}
lift :: forall {k} (a :: SYN k) b d g. (CategoryOf k) => (Interp a ~> Interp b) -> Term d g a -> Term d g b
lift f (MkTerm t) = MkTerm (f . t)

-- | Two terms side by side. A variable both use is copied.
{-# INLINE (**) #-}
(**)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Monoidal k, Merge g1 g2)
  => Term d g1 a -> Term d g2 b -> Term d (Union g1 g2) (a :** b)
MkTerm f ** MkTerm g = MkTerm ((f M.** g) . merge @g1 @g2)

-- | Two new variables @n@ and @n + 1@, of types @a@ and @b@, for the body of a 'split' whose
-- context is @g'@: the tensor @a ':**' b@, given from the context @g@, next to @r@, what the body
-- uses besides them.
{-# INLINE push2 #-}
push2
  :: forall {k} n (a :: SYN k) b g' r1 r g
   . (Monoidal k, KnownObj a, KnownObj b, BindVar (n + 1) b g' r1, BindVar n a r1 r, Merge r g)
  => (Interp (Mul g) ~> Interp a ** Interp b)
  -> Interp (Mul (Union r g)) ~> Interp (Mul g')
push2 p =
  withCtxOb @r
    ( withSynOb @b
        ( bindVar @(n + 1) @b @g' @r1
            . (bindVar @n @a @r1 @r M.** obj @(Interp b))
            . associatorInv' (ctxOb @r) (synOb @a) (synOb @b)
            . (ctxOb @r M.** p)
            . merge @r @g
        )
    )

-- | Take a tensor apart: the continuation gets a variable for each side.
{-# INLINE split #-}
split
  :: forall {k} d g g' r1 r (a :: SYN k) b c da db
   . (Monoidal k, KnownObj a, KnownObj b, BindVar (d + 1) b g' r1, BindVar d a r1 r, Merge r g)
  => Term d g (a :** b)
  -> (Term da '[ '(d, a)] a -> Term db '[ '(d + 1, b)] b -> Term (d + 2) g' c)
  -> Term d (Union r g) c
split (MkTerm p) k = case k (var @d @a) (var @(d + 1) @b) of
  MkTerm body -> MkTerm (body . push2 @d @a @b @g' @r1 @r @g p)

-- | The unit, which uses no variables.
{-# INLINE unit #-}
unit :: forall {k} d. (Monoidal k) => Term d ('[] :: Ctx k) I
unit = MkTerm id

-- | The same morphism at another type expression for the same object, and at any depth: between
-- @'F' (a '**' b)@ and @'F' a ':**' 'F' b@, say, so that a pattern can take it apart, or between a
-- type and its 'Dn'. The polarity may change, the morphism does not.
{-# INLINE recast #-}
recast :: forall {k} (a :: SYN k) b d d' g. (Interp a ~ Interp b) => Term d g a -> Term d' g b
recast (MkTerm f) = MkTerm f

type DepthOf :: Type -> Nat
type family DepthOf t where
  DepthOf (Term d g a) = d

type CtxOf :: forall k. Type -> Ctx k
type family CtxOf t where
  CtxOf (Term d g a) = g

type TyOf :: forall k. Type -> SYN k
type family TyOf t where
  TyOf (Term d g a) = a
