{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": functions and traces. It exports everything, also what
-- the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Closed where

import Data.Kind (Constraint, Type)
import Prelude (type (~))

import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Strength (Costrong, trace)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..))

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

infixl 8 !

-- | A function: the body receives the argument through a pattern (see /Patterns/). This needs the
-- category to be closed.
{-# INLINE lam #-}
lam
  :: forall {k} d r (a :: SYN k) b t cont
   . (Closed k, Binds (~>) d r a b t cont)
  => (t -> cont)
  -> Term d r (a :-> b)
lam k = withCtxOb @r (withSynOb @a (MkTerm (curry @k @(Interp (Mul r)) @(Interp a) (bound @(~>) @d @r @a @b k))))

-- | Trace: the body receives the value fed back through a pattern (see /Patterns/), and returns
-- it again next to the result. This needs the category to be traced.
{-# INLINE loop #-}
loop
  :: forall {k} {p} (u :: SYN k) b d r t cont
   . (Costrong M.Tensor p, M.SymMonoidal k, KnownObj b, Binds p d r u (b :** u) t cont)
  => (t -> cont)
  -> TermP p d r b
loop k =
  withCtxOb @r
    ( withSynOb @u
        (withSynOb @b (MkTerm (trace @p @(Interp u) @(Interp (Mul r)) @(Interp b) (bound @p @d @r @u @(b :** u) k))))
    )

-- | Function application. A variable both the function and its argument use is copied.
-- Explicit exponentials determine their result syntax. Embedded function objects, such as
-- results of '(-<)', take their result syntax from the surrounding term.
type Apply :: forall {k}. CAT k -> Type -> Type -> Type -> Constraint
class Apply (p :: CAT k) f x r | f -> p where
  (!)
    :: (Closed k, M.MonoidalProfunctor p, KnownObj (TyOf @k x), KnownObj (TyOf @k r), Merge (CtxOf @k f) (CtxOf @k x))
    => f -> x -> r

instance (x ~ TermP p d g2 a, r ~ TermP p d (Union g1 g2) b) => Apply p (TermP p d g1 (a :-> b :: SYN k)) x r where
  {-# INLINE (!) #-}
  (!) = applyTerm @a @b

instance
  (f ~ (Interp a ~~> Interp b), x ~ TermP p d g2 a, r ~ TermP p d (Union g1 g2) b)
  => Apply p (TermP p d g1 (F f :: SYN k)) x r
  where
  {-# INLINE (!) #-}
  (!) = applyTerm @a @b

{-# INLINE applyTerm #-}
applyTerm
  :: forall {k} (a :: SYN k) b p d g1 g2 f
   . (Closed k, M.MonoidalProfunctor p, KnownObj a, KnownObj b, Merge g1 g2, Interp f ~ (Interp a ~~> Interp b))
  => TermP p d g1 f
  -> TermP p d g2 a
  -> TermP p d (Union g1 g2) b
applyTerm (MkTerm f) (MkTerm x) =
  withSynOb @a
    ( withSynOb @b
        (MkTerm (dimap (merge @g1 @g2) (apply @k @(Interp a) @(Interp b)) (f M.** x)))
    )
