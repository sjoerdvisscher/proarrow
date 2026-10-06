{-# LANGUAGE QualifiedDo #-}

-- | Call by push value in "Proarrow.Tools.SMC": values are pure, and effects live in computations,
-- terms of 'Up', which run when they are bound. The target is 'CPS' @(m ())@ for a monad @m@. Its
-- morphisms are plain functions, and a computation of an @a@ is @(a -> m ()) -> m ()@: an action
-- of @m@ that passes its result on. With @m@ 'IO' the programs below read, print and return; the
-- tests run them in a writer monad, so that the order of the effects can be checked.
module Examples.Cbpv (test) where

import Data.Kind (Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding ((**))

import Proarrow.Category.Instance.Cps (CPS (..), Cps (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..))
import Proarrow.Core (CategoryOf (..))
import Proarrow.Testing (check)
import Proarrow.Tools.SMC (SYN (F, I, (:**)), Up, dup, force, lam, lift, ret, thunk, toSMC, unit, (!), (**))
import Proarrow.Tools.SMC qualified as SMC

-- | The category: functions, with the actions @m ()@ as the answer object.
type K m = CPS (m () :: Type)

-- | A value type.
type V m a = F (C a :: K m)

-- | A computation that produces an @a@: a term of it is @(a -> m ()) -> m ()@.
type Comp m a = Up (V m a)

-- | A computation for its effect alone.
type Eff m = Up (I :: SYN (K m))

-- | An action as a computation. The action runs when the computation is bound.
act :: forall m a d. (Monad m) => m a -> SMC.Term d '[] (Comp m a)
act m = lift @I @(Comp m a) (Cps \() k -> m >>= k) unit

-- | An action for its effect alone.
act_ :: forall m d. (Monad m) => m () -> SMC.Term d '[] (Eff m)
act_ m = lift @I @(Eff m) (Cps \() k -> m >>= k) unit

-- | A function from a value to an action, as a function from the value to its effect.
effect :: forall m a d g. (Monad m) => (a -> m ()) -> SMC.Term d g (V m a) -> SMC.Term d g (Eff m)
effect f = lift @(V m a) @(Eff m) (Cps \a k -> f a >>= k)

-- | A constant.
val :: forall m a d. a -> SMC.Term d '[] (V m a)
val a = lift @I @(V m a) (Cps (const a)) unit

-- | Run a closed computation: give its result to a final continuation.
run :: (Unit ~> Dual (Dual (C a :: K m))) -> (a -> m ()) -> m ()
run (Cps p) k = p () k

-- * Programs

-- | Read two numbers, tell their sum, and return it. The reads happen in the order of the binds,
-- and the sum is a value, copied with 'dup' to be both told and returned.
addT :: forall m. (Monad m) => m Int -> m Int -> (String -> m ()) -> Unit ~> Dual (Dual (C Int :: K m))
addT readX readY say = toSMC @I @(Comp m Int) \() -> SMC.do
  x <- act readX
  y <- act readY
  (s, s') <- dup (plus (x ** y))
  () <- effect (say . ("sum " ++) . show) s
  ret s'

plus :: forall m d g. SMC.Term d g (V m Int :** V m Int) -> SMC.Term d g (V m Int)
plus = lift @(V m Int :** V m Int) @(V m Int) (Cps (uncurry (+)))

-- | Two computations made in one order and run in the other. A computation is a value until it is
-- bound, so the effects happen in the order of the binds, not in the order the actions were
-- written.
reversedT :: forall m. (Monad m) => m () -> m () -> Unit ~> Dual (Dual (C () :: K m))
reversedT a b = toSMC @I @(Eff m) \() -> SMC.do
  (first, second) <- act_ a ** act_ b
  () <- second
  () <- first
  ret unit

-- | A computation that is made and dropped. Its effect never happens: dropping it is dropping a
-- value, which needs nothing but a comonoid.
droppedT :: forall m. (Monad m) => m () -> Unit ~> Dual (Dual (C () :: K m))
droppedT a = toSMC @I @(Eff m) \() -> SMC.do
  () <- SMC.drop (act_ a)
  ret unit

-- | A computation stored with 'thunk', so that binding it does not run it, copied as the value it
-- then is, and run twice with 'force'.
storedT :: forall m. (Monad m) => m () -> Unit ~> Dual (Dual (C () :: K m))
storedT a = toSMC @I @(Eff m) \() -> SMC.do
  t <- thunk (act_ a)
  (t1, t2) <- dup t
  () <- force t1
  () <- force t2
  ret unit

-- | A function from a value to a computation, made once and applied twice. Its effect happens at
-- each application, not when the function is made.
twiceT :: forall m. (Monad m) => (Int -> m ()) -> Unit ~> Dual (Dual (C () :: K m))
twiceT say = toSMC @I @(Eff m) \() -> SMC.do
  (f, f') <- dup (lam (effect say))
  () <- f ! val 1
  () <- f' ! val 2
  ret unit

-- * Tests

-- | The writer monad the tests run in.
type W = (,) [String]

tell :: String -> W ()
tell s = ([s], ())

-- | The effects of a program, with its result told last.
logOf :: (Unit ~> Dual (Dual (C a :: K W))) -> (a -> String) -> [String]
logOf p result = fst (run p (tell . result))

test :: TestTree
test =
  testGroup
    "Call by push value (Proarrow.Tools.SMC)"
    [ testProperty "actions run in the order of the binds, and the result comes last" $
        check
          "wrong effects"
          ( logOf (addT (tell "read x" >> pure 1) (tell "read y" >> pure 2) tell) (("return " ++) . show)
              == ["read x", "read y", "sum 3", "return 3"]
          )
    , testProperty "computations are values: made in one order, run in the other" $
        check "wrong effects" (logOf (reversedT (tell "a") (tell "b")) (const "done") == ["b", "a", "done"])
    , testProperty "a stored computation is bound without running, and runs at each force" $
        check "wrong effects" (logOf (storedT (tell "a")) (const "done") == ["a", "a", "done"])
    , testProperty "a dropped computation has no effect" $
        check "wrong effects" (logOf (droppedT (tell "never")) (const "done") == ["done"])
    , testProperty "a function's effect happens at each application" $
        check "wrong effects" (logOf (twiceT (tell . ("say " ++) . show)) (const "done") == ["say 1", "say 2", "done"])
    ]
