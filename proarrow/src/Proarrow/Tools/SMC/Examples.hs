{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | Examples of "Proarrow.Tools.SMC". They are compiled at @k = 'Data.Kind.Type'@, where the result
-- can be run.
module Proarrow.Tools.SMC.Examples
  ( swapT
  , applyT
  , curryT
  , rotT
  , traceT
  , loopT
  , loopCC
  , snakeT
  , combineDualT
  , distT
  , swapEitherT
  , bothWaysT
  , dniT
  , dneT
  , bindT
  , contraT
  , parSwapT
  , weakDistT
  , matMulT
  , traceIdxT
  , hadamardT
  , snakeDualT
  ) where

import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..), Par)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Monoidal.Hypergraph (Frobenius)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strength (TracedMonoidal)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Core (CategoryOf (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))

import Proarrow.Tools.SMC
import Proarrow.Tools.SMC qualified as SMC

-- | Swap a tensor.
--
-- >>> import Prelude (Bool (..))
-- >>> swapT @Bool @Bool (True, False)
-- (False,True)
swapT :: forall {k} (a :: k) b. (SymMonoidal k, Ob a, Ob b) => a ** b ~> b ** a
swapT = toSMC @(F a :** F b) \(a, b) -> b ** a

-- | Apply a function to an argument, both in a tensor.
--
-- >>> import Prelude (Bool (..), not)
-- >>> applyT @Bool @Bool (not, True)
-- False
applyT :: forall {k} (a :: k) b. (Closed k, SymMonoidal k, Ob a, Ob b) => (a ~~> b) ** a ~> b
applyT = toSMC @((F a :-> F b) :** F a) (\p -> split p (\f x -> f ! x))

-- | Curry the tensor.
--
-- >>> import Prelude (Bool (..))
-- >>> curryT @Bool @Bool True False
-- (True,False)
curryT :: forall {k} (a :: k) b. (Closed k, SymMonoidal k, Ob a, Ob b) => a ~> b ~~> a ** b
curryT = toSMC @(F a) @(F b :-> F a :** F b) (\x -> lam (\y -> x ** y))

-- | Rotate a triple, with a triple pattern.
--
-- >>> import Prelude (Bool (..), Int)
-- >>> rotT @Int @Bool @Int ((1, True), 2)
-- ((True,2),1)
rotT :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => a ** b ** c ~> b ** c ** a
rotT = toSMC @(F a :** F b :** F c) \(a, b, c) -> b ** c ** a

-- | Trace out @u@ with a @rec@ block. In 'Data.Kind.Type' the trace is a lazy fixed point.
--
-- >>> import Prelude (Int, take)
-- >>> traceT @Int @[Int] @[Int] (\(a, u) -> (take 3 u, a : u)) 1
-- [1,1,1]
traceT :: forall {k} (a :: k) b u. (TracedMonoidal k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
traceT h = toSMC @(F a) \a -> SMC.do
  rec (b, u) <- lift @(F a :** F u) @(F b :** F u) h (a ** u)
  b

-- | Trace out @u@ with 'loop'.
--
-- >>> import Prelude (Int, take)
-- >>> loopT @Int @[Int] @[Int] (\(a, u) -> (take 3 u, a : u)) 1
-- [1,1,1]
loopT :: forall {k} (a :: k) b u. (TracedMonoidal k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
loopT h = toSMC @(F a) \a -> loop @(F u) \u -> lift @(F a :** F u) @(F b :** F u) h (a ** u)

-- | A trace from the duality alone, so for any compact closed category: feed @u@ in along one
-- end of a new pair and join its new value with the other end.
loopCC :: forall {k} (a :: k) b u. (CompactClosed k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
loopCC h = toSMC @(F a) \a -> SMC.do
  (u, u') <- produce
  (b, v) <- lift @(F a :** F u) @(F b :** F u) h (a ** u)
  () <- annihilate u' v
  b

-- | A snake: create a pair, join its dual with the input, and continue with the other end. By the
-- zigzag law it is the identity. The input is older than the pair, so it sits to the left of it,
-- and the join needs a swap.
snakeT :: forall {k} (a :: k). (CompactClosed k, Ob a) => a ~> a
snakeT = toSMC @(F a) \x -> SMC.do
  (a, a') <- produce
  () <- annihilate a' x
  a

-- | The inverse of 'distribDual': make a pair for @a ** b@, and annihilate the two halves of its
-- plain end with the given duals.
combineDualT :: forall {k} (a :: k) b. (CompactClosed k, Ob a, Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDualT = toSMC @(Not (F a) :** Not (F b)) @(Not (F a :** F b)) \(da, db) -> SMC.do
  (ab, ab') <- produce
  (a, b) <- ab
  () <- annihilate da a
  () <- annihilate db b
  ab'

-- | The tensor distributes over the coproduct: the shared @a@ goes to whichever branch is taken.
--
-- >>> import Prelude (Bool (..), Char, Either (..), Int)
-- >>> distT @Int @Bool @Char (1, Left True)
-- Left (1,True)
distT
  :: forall {k} (a :: k) b c. (Distributive k, SymMonoidal k, Ob a, Ob b, Ob c) => a ** (b || c) ~> (a ** b) || (a ** c)
distT = toSMC @(F a :** (F b :|| F c)) \(a, bc) ->
  caseOf bc (\b -> inl (a ** b)) (\c -> inr (a ** c))

-- | Swap a coproduct, with nothing to share.
--
-- >>> import Prelude (Bool (..), Either (..), Int)
-- >>> swapEitherT @Int @Bool (Left 1)
-- Right 1
swapEitherT :: forall {k} (a :: k) b. (Distributive k, SymMonoidal k, Ob a, Ob b) => a || b ~> b || a
swapEitherT = toSMC @(F a :|| F b) \x -> caseOf x (\a -> inr a) (\b -> inl b)

-- | A pair both as it is and swapped: the second alternative takes the pair apart.
--
-- >>> import Prelude (Bool (..), Int)
-- >>> bothWaysT @Int @Bool (1, True)
-- ((1,True),(True,1))
bothWaysT
  :: forall {k} (a :: k) b. (SymMonoidal k, HasBinaryProducts k, Ob a, Ob b) => a ** b ~> (a ** b) && (b ** a)
bothWaysT = toSMC @(F a :** F b) \p -> with p (split p \x y -> y ** x)

-- | Double negation introduction: a consumer of a consumer of @a@ hands it the @a@. This is
-- 'ret', written out.
dniT :: forall {k} (a :: k). (Dialogue k, Ob a) => a ~> Dual (Dual a)
dniT = toSMC @(F a) @(Up (F a)) \x -> cont (x |>)

-- | Double negation elimination, the classical direction: a computation is its value. Binding its
-- consumer with 'cont' and cutting would only give the computation back.
dneT :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
dneT = toSMC @(Up (F a)) @(F a) \nn -> classical nn

-- | Sequencing: run the input computation, and continue with @f@ on its value. In a category with
-- @'Dual' a = a ~~> r@ this is the bind of the continuation monad.
bindT :: forall {k} (a :: k) b. (Dialogue k, Ob a, Ob b) => (a ~> Dual (Dual b)) -> Dual (Dual a) ~> Dual (Dual b)
bindT f = toSMC @(Up (F a)) @(Up (F b)) \m -> SMC.do
  x <- m
  lift @(F a) @(Up (F b)) f x

-- | Contraposition: a consumer of @b@ consumes @a@ through @f@.
contraT :: forall {k} (a :: k) b. (Dialogue k, Ob a, Ob b) => (a ~> b) -> Dual b ~> Dual a
contraT f = toSMC @(Not (F b)) @(Not (F a)) \nb -> cont \x -> cut nb (lift @(F a) @(F b) f x)

-- | Par is symmetric: bind both outputs and hand them to the input the other way round. This is
-- 'Proarrow.Category.Monoidal.Dialogue.parSwap'.
parSwapT :: forall {k} (a :: k) b. (Dialogue k, Ob a, Ob b) => Par a b ~> Par b a
parSwapT = toSMC @(F a :## F b) @(F b :## F a) \p -> cont \(kb, ka) -> ka ** kb |> p

-- | Linear (weak) distributivity, @a ⊗ (b ⅋ c) ⊸ (a ⊗ b) ⅋ c@: the @b@ the input emits is paired
-- with @a@ and sent to the first output, and its @c@ goes to the second. This is
-- 'Proarrow.Category.Monoidal.Dialogue.weakDistL'.
weakDistT
  :: forall {k} (a :: k) b c
   . (Dialogue k, Ob a, Ob b, Ob c)
  => a ** Par b c ~> Par (a ** b) c
weakDistT = toSMC @(F a :** (F b :## F c)) @((F a :** F b) :## F c) \(a, bc) ->
  cont \(kab, kc) -> cont (\b -> a ** b |> kab) ** kc |> bc

-- | Composition in index notation, as matrix multiplication: the entry at @i@ and @k@ is the sum over
-- @j@ of the entries of @f@ and @g@. It is @g . f@.
matMulT :: forall {k} (a :: k) b c. (SymMonoidal k, Frobenius b, Frobenius c, Ob a) => (a ~> b) -> (b ~> c) -> a ~> c
matMulT f g = toSMC @(F a) \i -> sumOver @(F c) \k -> sumOver @(F b) \j ->
  delta (lift f i) j *^ delta (lift g j) k *^ k

-- | The trace in index notation: the sum of the diagonal entries.
traceIdxT :: forall {k} (a :: k). (SymMonoidal k, Frobenius a) => (a ~> a) -> Unit ~> (Unit :: k)
traceIdxT f = toSMC @I \() -> sumOver @(F a) \i -> delta (lift f i) i

-- | The entrywise product of two morphisms: two boxes that produce the same index.
hadamardT :: forall {k} (a :: k) b. (SymMonoidal k, Frobenius a, Frobenius b) => (a ~> b) -> (a ~> b) -> a ~> b
hadamardT f g = toSMC @(F a) \i -> sumOver @(F b) \j ->
  delta (lift f i) j *^ delta (lift g i) j *^ j

-- | The snake on the dual: join the input with the first end of a new pair, and continue with the
-- second. Here the wires meet in the order they come, so no swap is needed.
snakeDualT :: forall {k} (a :: k). (CompactClosed k, Ob a) => Dual a ~> Dual a
snakeDualT = toSMC @(Not (F a)) \x -> SMC.do
  (a, a') <- produce
  () <- annihilate x a
  a'
