{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": index notation for categories whose index types are
-- Frobenius algebras. It exports everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Frobenius where

import Proarrow.Category.Monoidal (Monoidal (..), rightUnitorInvWith)
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, cap)
import Proarrow.Core (Promonad (..))
import Proarrow.Monoid (Monoid (..))

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

infixl 7 *^
infixl 7 ^*

-- | An index summed over: the binder's variable is fed by the unit of its type's monoid, which,
-- copied to every use, is the sum over all the values the index can take. The body receives the
-- index through a pattern (see /Patterns/).
{-# INLINE sumOver #-}
sumOver
  :: forall {k} (a :: SYN k) d r b t cont
   . (Monoidal k, Frobenius (Interp a), Binds d r a b t cont)
  => (t -> cont)
  -> Term d r b
sumOver k =
  withCtxOb @r
    ( withSynOb @a
        ( MkTerm
            (bound @d @r @a @b k . rightUnitorInvWith @(Interp (Mul r)) (mempty @(Interp a)))
        )
    )

-- | The Kronecker delta: the scalar that says two wires of an index type carry the same value. It
-- is the cap of the Frobenius algebra, @'Proarrow.Monoid.counit' . 'Proarrow.Monoid.mappend'@.
{-# INLINE delta #-}
delta
  :: forall {k} (a :: SYN k) d g1 g2
   . (Frobenius (Interp a), KnownObj a, Merge g1 g2)
  => Term d g1 a -> Term d g2 a -> Term d (Union g1 g2) I
delta x y = lift @(a :** a) @I (cap @(Interp a)) (x ** y)

-- | A term multiplied by a scalar on its left. At 'I' it is the product of two scalars.
{-# INLINE (*^) #-}
(*^)
  :: forall {k} d g1 g2 (a :: SYN k)
   . (Monoidal k, KnownObj a, Merge g1 g2)
  => Term d g1 I -> Term d g2 a -> Term d (Union g1 g2) a
s *^ x = lift @(I :** a) @a (withSynOb @a (leftUnitor @k @(Interp a))) (s ** x)

-- | A term multiplied by a scalar on its right.
{-# INLINE (^*) #-}
(^*)
  :: forall {k} d g1 g2 (a :: SYN k)
   . (Monoidal k, KnownObj a, Merge g1 g2)
  => Term d g1 a -> Term d g2 I -> Term d (Union g1 g2) a
x ^* s = lift @(a :** I) @a (withSynOb @a (rightUnitor @k @(Interp a))) (x ** s)
