{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | The linear logic connectives of "Proarrow.Tools.SMC", each tested where it lives.
--
-- * Duals over 'FinRel', which is compact closed and also traced: the snake equations,
--   'combineDual', and the trace built from the duality agreeing with 'FinRel''s own.
-- * Classical reasoning in the Kleisli category of the continuation monad, which is
--   *-autonomous but not compact closed: its dual is @a -> r@, so terms can be run on values and
--   continuations. And 'annihilate' in 'LINEAR', which is isomix but not compact closed.
-- * The additives over 'FinRel', which is distributive: case analysis agrees with the
--   distributor, and 'with' with the pairing.
-- * Par, built with 'Proarrow.Tools.SMC.par' and consumed with 'Proarrow.Tools.SMC.both', run in
--   'LINEAR' on values and checked against its own par functions, and over 'FinRel', where par is
--   the tensor.
module Examples.LinearLogic (test, snakePicture) where

import Data.List (isInfixOf)
import Data.Type.Nat (Nat (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (fst, id, snd, (**), (.))

import Proarrow.Category.Instance.FinRel (FINREL (..))
import Proarrow.Category.Instance.IntConstruction (INT (..), IntConstruction (..))
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.Linear (LINEAR (..), unLinear)
import Proarrow.Category.Instance.Linear qualified as Lin
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), type (**))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..), combineDual)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Monoidal.IsoMix (IsoMix)
import Proarrow.Category.Monoidal.StarAutonomous
  ( Par
  , StarAutonomous (..)
  , doubleNegDefault
  , doubleNegInvDefault
  , parSwap
  , weakDistL
  , weakDistR
  )
import Proarrow.Category.Monoidal.StarAutonomous qualified as SA
import Proarrow.Category.Monoidal.Strength (trace)
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Promonad.Cont (Cont (..))
import Proarrow.Testing (check, genNamed)
import Proarrow.Tools.Diagrams.Svg qualified as Svg
import Proarrow.Tools.SMC
  ( SYN (D, F, (:**))
  , annihilate
  , both
  , bothWaysT
  , combineDualT
  , contraT
  , distT
  , dneT
  , dniT
  , emit
  , loopCC
  , parSwapT
  , rotT
  , snakeDualT
  , snakeT
  , swapEitherT
  , toSMC
  , weakDistT
  , (|>)
  , type (:##)
  )
import Proarrow.Tools.SMC qualified as SMC
import Props.FinRel ()

test :: TestTree
test = testGroup "Linear logic (Proarrow.Tools.SMC)" [duality, classical, additives, parTests]

type F1 = FR (S Z)
type F2 = FR (S (S Z))
type F3 = FR (S (S (S Z)))

-- * Duals

-- | The snake on the dual as a string diagram: a cup and a cap.
snakePicture :: String
snakePicture = Svg.render (snakeDualT @(Svg.S '[Svg.Wire "a"]))

duality :: TestTree
duality =
  testGroup
    "Duality"
    [ testProperty "snake is the identity (FinRel 2)" $ check "differs from id" (snakeT @F2 == id)
    , testProperty "snake is the identity (FinRel 3)" $ check "differs from id" (snakeT @F3 == id)
    , testProperty "the snake on the dual is the identity (FinRel 2)" $ check "differs from id" (snakeDualT @F2 == id)
    , testProperty "the snake draws" $ check "not an SVG document" ("<svg" `isInfixOf` snakePicture)
    , testProperty "a triple pattern is the left-nested pairs (FinRel 2, 1, 3)" $
        check
          "differs"
          ( toSMC @(F F2 :** F F1 :** F F3) (\(x, y, z) -> z SMC.* x SMC.* y)
              == toSMC @(F F2 :** F F1 :** F F3) (\((x, y), z) -> z SMC.* x SMC.* y)
          )
    , testProperty "a quadruple pattern is the left-nested pairs (FinRel 2, 1, 3, 2)" $
        check
          "differs"
          ( toSMC @(F F2 :** F F1 :** F F3 :** F F2) (\(w, x, y, z) -> z SMC.* x SMC.* w SMC.* y)
              == toSMC @(F F2 :** F F1 :** F F3 :** F F2) (\(((w, x), y), z) -> z SMC.* x SMC.* w SMC.* y)
          )
    , testProperty "combineDual (FinRel 2, 3)" $
        check "differs from combineDual" (combineDualT @F2 @F3 == combineDual @F2 @F3)
    , -- the Int construction's duals swap the two halves; bigger objects than these get expensive
      testProperty "combineDual (Int construction over FinRel)" $
        check "differs from combineDual" $
          case (combineDualT @(I F1 F2) @(I F1 F1), combineDual @(I F1 F2) @(I F1 F1)) of
            (Int f, Int g) -> f == g
    , testProperty "combineDual inverts distribDual (FinRel 3, 2)" $
        check "not inverses" (combineDualT @F3 @F2 . distribDual @_ @F3 @F2 == id)
    , testProperty "the trace from the duality is FinRel's trace" $ do
        h <- genNamed @(F2 ** F2 ~> F3 ** F2) "h"
        check "differs from trace" (loopCC @F2 @F3 @F2 h == trace @(~>) @F2 @F2 @F3 h)
    , testProperty "the trace from the duality is FinRel's trace (other sizes)" $ do
        h <- genNamed @(F3 ** F1 ~> F2 ** F1) "h"
        check "differs from trace" (loopCC @F3 @F2 @F1 h == trace @(~>) @F1 @F3 @F2 h)
    ]

-- * Classical reasoning

type K = KLEISLI (Cont Int)

-- | Run a morphism of @K@ on a value and a continuation.
run :: (KL a :: K) ~> KL b -> a -> (b -> Int) -> Int
run (Kleisli (Cont m)) a k = m k a

incr :: (KL Int :: K) ~> KL Int
incr = Kleisli (Cont \k a -> k (a + 1) * 2)

-- Values, continuations, and elements and continuations of the dual and double dual of @Int@.
xs :: [Int]
xs = [0, 3, 7]

ks :: [Int -> Int]
ks = [(* 2), (+ 1)]

nns :: [(Int -> Int) -> Int]
nns = [\c -> c 3 + c 4, ($ 5)]

nnks :: [((Int -> Int) -> Int) -> Int]
nnks = [\nn -> nn (* 3), \nn -> nn id + 1]

nbs :: [Int -> Int]
nbs = [(* 5), subtract 1]

nks :: [(Int -> Int) -> Int]
nks = [($ 2), \g -> g 0 + g 9]

-- | Give an @a@ to its consumer and keep the @b@: needs only isomix.
annihilateT :: forall {k} (a :: k) b. (IsoMix k, SymMonoidal k, Ob a, Ob b) => Dual a ** a ** b ~> b
annihilateT = toSMC @(D (F a) :** F a :** F b) \(na, a, b) -> SMC.do
  () <- annihilate na a
  b

classical :: TestTree
classical =
  testGroup
    "Classical"
    [ testProperty "double negation elimination after introduction is the identity" $
        check "differs" (and [run (dneT @(KL Int) . dniT) x k == k x | x <- xs, k <- ks])
    , testProperty "double negation introduction is doubleNegInv" $
        check "differs" (and [run (dniT @(KL Int)) x k == run (doubleNegInv @K @(KL Int)) x k | x <- xs, k <- nnks])
    , testProperty "double negation elimination is doubleNeg" $
        check "differs" (and [run (dneT @(KL Int)) nn k == run (doubleNeg @K @(KL Int)) nn k | nn <- nns, k <- ks])
    , testProperty "the continuation category's doubleNeg is doubleNegDefault" $
        check
          "differs"
          (and [run (doubleNeg @K @(KL Int)) nn k == run (doubleNegDefault @(KL Int :: K)) nn k | nn <- nns, k <- ks])
    , testProperty "the continuation category's doubleNegInv is doubleNegInvDefault" $
        check
          "differs"
          (and [run (doubleNegInv @K @(KL Int)) x k == run (doubleNegInvDefault @(KL Int :: K)) x k | x <- xs, k <- nnks])
    , -- each call of LINEAR's doubleNeg needs its own reference; a shared one returns stale values
      testProperty "double negation in LINEAR gives back every value" $
        check "differs" ([unLinear (doubleNeg @LINEAR @(L Int) . doubleNegInv) x | x <- [1 .. 1000]] == [1 .. 1000])
    , testProperty "double negation elimination after introduction in LINEAR, nested" $
        check "differs" ([unLinear (dneT @(L Int) . dneT . dniT . dniT) x | x <- [1 .. 100]] == [1 .. 100])
    , testProperty "annihilate in LINEAR" $
        check "differs" (and [unLinear (annihilateT @(L ()) @(L Bool)) ((\() -> (), ()), b) == b | b <- [False, True]])
    , testProperty "contraposition is dual" $
        check "differs" (and [run (contraT incr) nb k == run (dual incr) nb k | nb <- nbs, k <- nks])
    ]

-- * Additives

additives :: TestTree
additives =
  testGroup
    "Additives"
    [ testProperty "case analysis is the distributor (FinRel 2, 1, 3)" $
        check "differs from distL" (distT @F2 @F1 @F3 == distL @_ @F2 @F1 @F3)
    , testProperty "swapping a coproduct twice is the identity (FinRel 2, 3)" $
        check "differs from id" (swapEitherT @F3 @F2 . swapEitherT @F2 @F3 == id)
    , testProperty "the projections of a pair both ways are id and swap (FinRel 2, 3)" $ do
        check "fst differs from id" (fst @_ @(F2 ** F3) @(F3 ** F2) . bothWaysT @F2 @F3 == id)
        check "snd differs from swap" (snd @_ @(F2 ** F3) @(F3 ** F2) . bothWaysT @F2 @F3 == swap @_ @F2 @F3)
    ]

-- * Par

-- In 'LINEAR' a par is @'Lin.Not' ('Lin.Not' a, 'Lin.Not' b)@, and a component is read off by
-- giving the other side a consumer ('Lin.parAppL', 'Lin.parAppR'), which goes through LINEAR's
-- double negation.
type P a b = Lin.Not (Lin.Not a, Lin.Not b)

discard :: Bool %1 -> ()
discard = unLinear counit

discard2 :: (Bool, Bool) %1 -> ()
discard2 (a, b) = case discard a of () -> discard b

observe :: P a b -> Lin.Not a -> Lin.Not b -> (a, b)
observe q na nb = (Lin.parAppR (Lin.Par q) nb, Lin.parAppL (Lin.Par q) na)

-- | Read off pars of booleans, of a pair of booleans and a boolean, and the other way round.
observe2 :: P Bool Bool -> (Bool, Bool)
observe2 q = observe q discard discard

observeL :: P (Bool, Bool) Bool -> ((Bool, Bool), Bool)
observeL q = observe q discard2 discard

observeR :: P Bool (Bool, Bool) -> (Bool, (Bool, Bool))
observeR q = observe q discard discard2

unPar :: Lin.Par a b -> P a b
unPar (Lin.Par q) = q

-- Pars of two booleans, with what they hold, using the consumers in either order.
pars :: [(P Bool Bool, (Bool, Bool))]
pars = [(q, (x, y)) | x <- [False, True], y <- [False, True], q <- both' x y]
  where
    both' :: Bool -> Bool -> [P Bool Bool]
    both' x y = [\(na, nb) -> case na x of () -> nb y, \(na, nb) -> case nb y of () -> na x]

-- | A three way par rotated, with its three outputs bound by one pattern.
parRotT
  :: forall {k} (a :: k) b c
   . (StarAutonomous k, Ob a, Ob b, Ob c)
  => Dual (Dual (Par a b) ** Dual c) ~> Dual (Dual (Par b c) ** Dual a)
parRotT = toSMC @(F a :## F b :## F c) @(F b :## F c :## F a) \p -> emit \(kb, kc, ka) -> both ka kb SMC.* kc |> p

-- | A command passed on through 'emit' with the pattern @()@.
emitUnitT :: forall k. (StarAutonomous k) => Dual (Unit :: k) ~> Dual Unit
emitUnitT = toSMC @(D (SMC.I :: SYN k)) @(D SMC.I) \c -> emit \() -> c

-- | 'parSwapT' with the par consumed by 'both'.
parSwapBothT
  :: forall {k} (a :: k) b. (StarAutonomous k, Ob a, Ob b) => Par a b ~> Par b a
parSwapBothT = toSMC @(F a :## F b) @(F b :## F a) \p -> emit \(kb, ka) -> p |> both ka kb

type B = L Bool

parTests :: TestTree
parTests =
  testGroup
    "Par"
    [ testProperty "par swap hands the input both outputs the other way round, as parSwap does" $
        check
          "differs"
          ( and
              [ observe2 (unLinear (parSwapT @B @B) q) == (y, x) && observe2 (unLinear (parSwap @B @B) q) == (y, x)
              | (q, (x, y)) <- pars
              ]
          )
    , testProperty "par swap twice is the identity" $
        check "differs" (and [observe2 (unLinear (parSwapT @B @B . parSwapT) q) == xy | (q, xy) <- pars])
    , testProperty "consuming the par with both is the same" $
        check "differs" (and [observe2 (unLinear (parSwapBothT @B @B) q) == (y, x) | (q, (x, y)) <- pars])
    , testProperty "weak distributivity pairs the emitted b with a, as weakDistL and pairFst do" $
        check
          "differs"
          ( and
              [ all @[]
                  (== ((a, x), y))
                  [ observeL (unLinear (weakDistT @B @B @B) (a, q))
                  , observeL (unLinear (weakDistL @B @B @B) (a, q))
                  , observeL (unPar (Lin.pairFst (a, Lin.Par q)))
                  ]
              | a <- [False, True]
              , (q, (x, y)) <- pars
              ]
          )
    , testProperty "weakDistR pairs c with the emitted b, as pairSnd does" $
        check
          "differs"
          ( and
              [ all @[]
                  (== (x, (y, c)))
                  [observeR (unLinear (weakDistR @B @B @B) (q, c)), observeR (unPar (Lin.pairSnd (Lin.Par q, c)))]
              | c <- [False, True]
              , (q, (x, y)) <- pars
              ]
          )
    , testProperty "emit with a triple pattern rotates a three way par (FinRel 2, 1, 3)" $
        check "differs from rotT" (parRotT @F2 @F1 @F3 == rotT @F2 @F1 @F3)
    , testProperty "emit with the pattern () passes a command on (continuations)" $
        check
          "differs from id"
          (and [run (emitUnitT @K) c k == k c | c <- [const 3, const 7], k <- [($ ()), \g -> g () * 2]])
    , testProperty "par swap is parSwap and swap (FinRel 2, 3)" $ do
        check "differs from parSwap" (parSwapT @F2 @F3 == parSwap @F2 @F3)
        check "differs from swap" (parSwapT @F2 @F3 == swap @_ @F2 @F3)
    , testProperty "weak distributivity is weakDistL and the associator (FinRel 2, 1, 3)" $ do
        check "differs from weakDistL" (weakDistT @F2 @F1 @F3 == weakDistL @F2 @F1 @F3)
        check "differs from associatorInv" (weakDistT @F2 @F1 @F3 == associatorInv @_ @F2 @F1 @F3)
    , testProperty "weakDistR is the associator (FinRel 2, 1, 3)" $
        check "differs from associator" (weakDistR @F2 @F1 @F3 == associator @_ @F2 @F1 @F3)
    , testProperty "par on arrows is the tensor (FinRel)" $ do
        f <- genNamed @(F2 ~> F3) "f"
        g <- genNamed @(F1 ~> F2) "g"
        check "differs from f ** g" (SA.par f g == f ** g)
    ]
