{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": functions and traces. It exports everything, also what
-- the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Closed where

import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Strength (TracedMonoidal, trace)
import Proarrow.Core (CategoryOf (..), Promonad (..))

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
   . (Closed k, Binds d r a b t cont)
  => (t -> cont)
  -> Term d r (a :-> b)
lam k = withCtxOb @r (withSynOb @a (MkTerm (curry @k @(Interp (Mul r)) @(Interp a) (bound @d @r @a @b k))))

-- | Trace: the body receives the value fed back through a pattern (see /Patterns/), and returns
-- it again next to the result. This needs the category to be traced.
{-# INLINE loop #-}
loop
  :: forall {k} (u :: SYN k) b d r t cont
   . (TracedMonoidal k, KnownObj b, Binds d r u (b :** u) t cont)
  => (t -> cont)
  -> Term d r b
loop k =
  withCtxOb @r
    ( withSynOb @u
        (withSynOb @b (MkTerm (trace @(~>) @(Interp u) @(Interp (Mul r)) @(Interp b) (bound @d @r @u @(b :** u) k))))
    )

-- | Function application. A variable both the function and its argument use is copied.
{-# INLINE (!) #-}
(!)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Closed k, KnownObj a, KnownObj b, Merge g1 g2)
  => Term d g1 (a :-> b) -> Term d g2 a -> Term d (Union g1 g2) b
MkTerm f ! MkTerm x =
  withSynOb @a (withSynOb @b (MkTerm (apply @k @(Interp a) @(Interp b) . (f M.** x) . merge @g1 @g2)))
