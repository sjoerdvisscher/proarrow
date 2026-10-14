{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": inputs and outputs in dialogue categories, and duals.
-- It exports everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Dialogue where

import Data.Kind (Type)
import GHC.TypeNats (Nat)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor)
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..), dualityCounitSA)
import Proarrow.Category.Monoidal.IsoMix (IsoMix (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Core (CategoryOf (..), Profunctor, Promonad (..), arr, type (+->))

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

infixl 1 |>
infixl 7 :##

-- | A new pair of wires, a variable and its dual, from nothing: the unit of the duality. This
-- needs the category to be compact closed.
{-# INLINE produce #-}
produce :: forall {k} {p} (a :: SYN k) d. (CompactClosed k, Promonad p, KnownObj a) => TermP p d '[] (a :** Not a)
produce = withSynOb @a (MkTerm (arr (dualityUnit @k @(Interp a))))

-- | Join a dual and its wire into nothing: the counit of the duality, which an isomix category
-- has.
{-# INLINE annihilate #-}
annihilate
  :: forall {k} {p} (a :: SYN k) d g1 g2
   . (IsoMix k, MonoidalProfunctor p, KnownObj a, Merge g1 g2)
  => ConsumerP p d g1 a -> TermP p d g2 a -> TermP p d (Union g1 g2) I
annihilate x y = rmapT (withSynOb @a (dualityCounit @k @(Interp a))) (x ** y)

-- | A consumer of @a@: a term of its negation.
type ConsumerP :: forall {k}. k +-> k -> Nat -> Ctx k -> SYN k -> Type
type ConsumerP p d g a = TermP p d g (Not a)

type Consumer d g a = Term d g (Not a)

-- | A producer and a consumer meeting: a term of the unit of par.
type CommandP :: forall {k}. k +-> k -> Nat -> Ctx k -> Type
type CommandP p d g = TermP p d g (Not I)

type Command d g = Term d g (Not I)

-- | Par, the negation of the tensor of the negations, interpreted as 'Proarrow.Category.Monoidal.Dialogue.Par'.
type (:##) :: forall {k}. SYN k -> SYN k -> SYN k
type a :## b = Not (Not a :** Not b)

-- | A consumer meets a producer: @cut k t@ gives @t@ to @k@, like applying a continuation.
{-# INLINE cut #-}
cut
  :: forall {k} {p} (a :: SYN k) d g1 g2
   . (Dialogue k, MonoidalProfunctor p, KnownObj a, Merge g1 g2)
  => ConsumerP p d g1 a -> TermP p d g2 a -> CommandP p d (Union g1 g2)
cut x y = rmapT (withSynOb @a (dualityCounitSA @(Interp a))) (x ** y)

-- | 'cut' with the producer first, as System L writes @⟨t | k⟩@: @t |> k@ sends @t@ into @k@.
{-# INLINE (|>) #-}
(|>)
  :: forall {k} {p} (a :: SYN k) d g1 g2
   . (Dialogue k, MonoidalProfunctor p, KnownObj a, Merge g2 g1)
  => TermP p d g1 a -> ConsumerP p d g2 a -> CommandP p d (Union g2 g1)
t |> k = cut k t

-- | The binder of System L. @cont \\x -> c@ is a term of @'Not' a@: it receives an @a@ through the
-- pattern @x@ (see /Patterns/) and runs the command @c@ with it.
--
-- What that @a@ is depends on how the result is used. As a 'Consumer' of @a@, the @a@ is an input
-- and @cont@ is μ̃: the seller in a shop receives the order, @cont \\(name, card, replyTo) -> …@. As
-- a term of the negative type @'Not' a@ in its own right, the @a@ is the consumer of an output and
-- @cont@ is μ, Haskell's @callCC@: a computation @'Up' b@ receives the consumer of its result,
-- @cont \\k -> … |> k@; a par @b ':##' c@ receives a consumer for each side, @cont \\(kb, kc) -> …@;
-- and a command, @'Not' 'I'@, receives nothing, @cont \\() -> …@. A consumer of a par is a
-- computation, which a nested pair pattern runs to get at the consumers of its sides.
{-# INLINE cont #-}
cont
  :: forall {k} d r (a :: SYN k) t cont
   . (Dialogue k, Binds (~>) d r a (Not I) t cont)
  => (t -> cont)
  -> Term d r (Not a)
cont k =
  withCtxOb @r
    ( withSynOb @a
        ( MkTerm
            ( dual (rightUnitorInv @k @(Interp a))
                . linDist @k @(Interp (Mul r)) @(Interp a) @Unit (bound @(~>) @d @r @a @(Not I) k)
            )
        )
    )

-- | Store a term of a negative type as a value: the same morphism at the positive type @'Dn' n@,
-- which a bind names instead of running. This is call by push value's @thunk@, 'recast' to 'Dn'.
{-# INLINE thunk #-}
thunk :: forall {k} {p} (n :: SYN k) d g. TermP p d g n -> TermP p d g (Dn n)
thunk = recast

-- | A stored term at its negative type again, where a bind runs it. This is call by push value's
-- @force@, 'recast' from 'Dn'.
{-# INLINE force #-}
force :: forall {k} {p} (n :: SYN k) d g. TermP p d g (Dn n) -> TermP p d g n
force = recast

-- | A computation as its value again: double negation elimination, which only a *-autonomous
-- category has. There every type is equivalent to its shift, so the polarities collapse.
{-# INLINE classical #-}
classical
  :: forall {k} {p} (a :: SYN k) d g. (StarAutonomous k, Profunctor p, KnownObj a) => TermP p d g (Up a) -> TermP p d g a
classical = withSynOb @a (rmapT (doubleNeg @k @(Interp a)))
