{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": index notation for categories whose index types are
-- Frobenius algebras. It exports everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Frobenius where

import GHC.TypeNats (type (+))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor, rightUnitorInvWith)
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, cap)
import Proarrow.Core (Profunctor (..), Promonad (..))
import Proarrow.Monoid (Monoid (..))
import Prelude (type (~))

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
  :: forall {k} {p} (a :: SYN k) d r b t cont
   . (Profunctor p, Frobenius (Interp a), Binds p d r a b t cont)
  => (t -> cont)
  -> TermP p d r b
sumOver k =
  withCtxOb @r
    ( withSynOb @a
        ( MkTerm
            (lmap (rightUnitorInvWith @(Interp (Mul r)) (mempty @(Interp a))) (bound @p @d @r @a @b k))
        )
    )

-- | An index summed over, as 'sumOver', for a body that refers to the index as the variable of id
-- @d@ instead of through a pattern.
{-# INLINE sumVar #-}
sumVar
  :: forall {k} {p} (a :: SYN k) d g' g b
   . (Profunctor p, Frobenius (Interp a), KnownObj a, BindVar d a g' g)
  => TermP p (d + 1) g' b
  -> TermP p d g b
sumVar (MkTerm body) =
  withCtxOb @g
    ( withSynOb @a
        (MkTerm (lmap (bindVar @d @a @g' @g . rightUnitorInvWith @(Interp (Mul g)) (mempty @(Interp a))) body))
    )

-- | The Kronecker delta: the scalar that says two wires of an index type carry the same value. It
-- is the cap of the Frobenius algebra, @'Proarrow.Monoid.counit' . 'Proarrow.Monoid.mappend'@.
{-# INLINE delta #-}
delta
  :: forall {k} {p} (a :: SYN k) d g1 g2
   . (MonoidalProfunctor p, Frobenius (Interp a), KnownObj a, Merge g1 g2)
  => TermP p d g1 a -> TermP p d g2 a -> TermP p d (Union g1 g2) I
delta x y = rmapT (cap @(Interp a)) (x ** y)

-- | A term multiplied by a scalar on its left. The scalar's type interprets to 'Unit',
-- including both 'I' and @'F' Unit@. At 'I' it is the product of two scalars.
{-# INLINE (*^) #-}
(*^)
  :: forall {k} {p} d g1 g2 (a :: SYN k) s
   . (MonoidalProfunctor p, KnownObj a, Merge g1 g2, Interp s ~ Unit)
  => TermP p d g1 s -> TermP p d g2 a -> TermP p d (Union g1 g2) a
s *^ x = withSynOb @a (rmapT (leftUnitor @k @(Interp a)) (s ** x))

-- | A term multiplied by a scalar on its right.
{-# INLINE (^*) #-}
(^*)
  :: forall {k} {p} d g1 g2 (a :: SYN k) s
   . (MonoidalProfunctor p, KnownObj a, Merge g1 g2, Interp s ~ Unit)
  => TermP p d g1 a -> TermP p d g2 s -> TermP p d (Union g1 g2) a
x ^* s = withSynOb @a (rmapT (rightUnitor @k @(Interp a)) (x ** s))
