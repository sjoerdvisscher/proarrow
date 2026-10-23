{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}

-- | Index notation in "Proarrow.Tools.SMC", checked against the structure of the category: in
-- 'FinRel', where a sum over an index is "there is", and in 'Mat' over 'Int', where it is a sum of
-- numbers.
module Props.SMC (test, name) where

import Control.Arrow qualified as A
import Control.Monad.Fix (MonadFix)
import Data.Bool (bool)
import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (toList)
import Data.Map.Strict qualified as M
import Data.Type.Nat (Nat (..), Nat2, Nat3)
import Data.Vec.Lazy (Vec (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (TestOptions (..), testProperty, testPropertyWith)
import Prelude hiding (id, mappend, mempty, (**), (.))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.FinRel (FINREL (..))
import Proarrow.Category.Instance.Mat (Mat (..), MatK (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Closed qualified as Closed
import Proarrow.Category.Monoidal.Hypergraph (Hypergraph, cap, cup)
import Proarrow.Category.Monoidal.Strictified (Fold, Strictified (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj, (\\))
import Proarrow.Functor (Prelude (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Profunctor.Instance.Arrow (Arr (..))
import Proarrow.Profunctor.Instance.Star (unStar, pattern Star)
import Proarrow.Testing (check, expect, genNamed)
import Proarrow.Testing.Laws (defaultTestOptions)
import Proarrow.Tools.Einsum (EinsumType, Tensor, einsum)
import Proarrow.Tools.SMC (SYN (..), delta, ifThenElse, liftF, returnA, sumOver, toSMC, toSMC1, unit, (*^), (-<), (^*))
import Proarrow.Tools.SMC qualified as SMC
import Proarrow.Tools.SMC.Examples (hadamardT, matMulT, traceIdxT)
import Props.FinRel ()
import Props.Mat ()

type F2 = FR (S (S Z))
type F3 = FR (S (S (S Z)))
type F4 = FR (S (S (S (S Z))))

type M2 = M Nat2 :: MatK Int
type M3 = M Nat3 :: MatK Int

-- | The transpose in index notation: the entry at @j@ and @i@ is the entry of @f@ at @i@ and @j@.
transposeT :: Mat M2 M3 -> Mat M3 M2
transposeT f = toSMC1 \j -> sumOver @(F M2) \i -> delta (f -< i) j *^ i

-- | A morphism as a tensor with an index for its input and one for its output.
name :: forall {k} (a :: k) b. (Hypergraph k) => a ~> b -> Tensor '[a, b]
name f = Str ((obj @a ** f) . cup @a) \\ f

-- | Matrix multiplication at the type 'EinsumType' computes, which is checked by compiling it.
matMulE :: EinsumType "ij,jk" '[ '[M2, M3], '[M3, M2]]
matMulE = einsum @"ij,jk"

-- The signature checks that case analysis needs ArrowChoice without ArrowApply.
choiceT
  :: (A.ArrowChoice arr)
  => arr (Either Int Bool) (Either Int Bool)
  -> arr (Int, Int) Int
  -> arr (Bool, Int) Int
  -> arr ((Either Int Bool, Int), Int) Int
choiceT select left right = unArr $ SMC.proc @((F (Either Int Bool) :** F Int) :** F Int) @(F Int) \((tag, n), m) -> SMC.do
  s <- Arr select -< tag
  if s
    then \x -> Arr left -< (x, n)
    else \b -> Arr right -< (b, m)

-- Reuse both the input and a bound value across later binds, then mix all their depths.
reuseAcrossBindsT
  :: (A.Arrow arr)
  => arr Int Int
  -> arr Int Int
  -> arr (Int, Int) Int
  -> arr Int ((Int, Int), (Int, Int))
reuseAcrossBindsT first second combine = unArr $ SMC.proc @(F Int) @(F ((Int, Int), (Int, Int))) \n -> SMC.do
  x <- Arr first -< n
  y <- Arr second -< x
  z <- Arr combine -< (x, n)
  returnA -< ((n, x), (y, z))

injectLeftT :: (A.Arrow arr) => arr Int Int -> arr Int (Either Int Bool)
injectLeftT f = unArr $ SMC.proc @(F Int) @(F Int :|| F Bool) \x -> SMC.inl (Arr f -< x)

injectRightT :: (A.Arrow arr) => arr Bool Bool -> arr Bool (Either Int Bool)
injectRightT f = unArr $ SMC.proc @(F Bool) @(F Int :|| F Bool) \x -> SMC.inr (Arr f -< x)

-- The signature checks that feedback needs ArrowLoop without ArrowApply or ArrowChoice.
arrowLoopT
  :: (A.ArrowLoop arr)
  => arr Int Int
  -> arr (Int, [Int]) (Int, [Int])
  -> arr Int Int
  -> arr Int Int
arrowLoopT before body after = unArr $ SMC.proc @(F Int) @(F Int) \n -> SMC.do
  x <- Arr before -< n
  y <- SMC.loop @(F [Int]) @(F Int) \u -> SMC.recast (Arr body -< (x, u))
  Arr after -< y

arrowRecT
  :: (A.ArrowLoop arr)
  => arr Int Int
  -> arr (Int, [Int]) (Int, [Int])
  -> arr Int Int
  -> arr Int Int
arrowRecT before body after = unArr $ SMC.proc @(F Int) @(F Int) \n -> SMC.do
  x <- Arr before -< n
  rec (y, u) <- Arr body -< (x, u)
  Arr after -< y

arrowRecCopyT :: (A.ArrowLoop arr) => arr (Int, [Int]) ([Int], [Int]) -> arr Int ([Int], [Int])
arrowRecCopyT body = unArr $ SMC.proc @(F Int) @(F ([Int], [Int])) \n -> SMC.do
  rec (ys, u) <- Arr body -< (n, u)
  Arr (A.second (A.arr (take 3))) -< (ys, u)

arrowRecDropT :: (A.ArrowLoop arr) => arr (Int, [Int]) (Int, [Int]) -> arr Int [Int]
arrowRecDropT body = unArr $ SMC.proc @(F Int) @(F [Int]) \n -> SMC.do
  rec (_ignored, u) <- Arr body -< (n, u)
  Arr (A.arr (take 3)) -< u

arrowRecDiscardT :: (A.ArrowLoop arr) => arr Int Int -> arr Int () -> arr Int ()
arrowRecDiscardT body after = unArr $ SMC.proc @(F Int) @(F ()) \n -> SMC.do
  rec _ignored <- Arr body -< n
  z <- Arr after -< n
  returnA -< z

starLoopT
  :: (MonadFix m)
  => (Int -> m Int)
  -> ((Int, [Int]) -> m (Int, [Int]))
  -> (Int -> m Int)
  -> Int
  -> m Int
starLoopT before body after =
  unPrelude
    . unStar
      ( SMC.proc @(F Int) @(F Int) \n -> SMC.do
          x <- Star (Prelude . before) -< n
          y <- SMC.loop @(F [Int]) @(F Int) \u -> SMC.recast (Star (Prelude . body) -< (x, u))
          Star (Prelude . after) -< y
      )

starRecT
  :: (MonadFix m)
  => (Int -> m Int)
  -> ((Int, [Int]) -> m (Int, [Int]))
  -> (Int -> m Int)
  -> Int
  -> m Int
starRecT before body after =
  unPrelude
    . unStar
      ( SMC.proc @(F Int) @(F Int) \n -> SMC.do
          x <- Star (Prelude . before) -< n
          rec (y, u) <- Star (Prelude . body) -< (x, u)
          Star (Prelude . after) -< y
      )

-- `\_ -> unit` binds a summed index that is not used, which is what is tested.
{- HLINT ignore test "Use const" -}
test :: TestTree
test =
  testGroup
    "SMC"
    [ testProperty "reuse across binds preserves variable identities and runs each effect once" $ do
        n <- genNamed @Int "input"
        let first = A.Kleisli (\x -> (["first"], x + 1))
            second = A.Kleisli (\x -> (["second"], x * 2))
            combine = A.Kleisli (\(x, input) -> (["combine"], x - input))
            run :: Int -> ([String], ((Int, Int), (Int, Int)))
            run = A.runKleisli (reuseAcrossBindsT first second combine)
        expect "values and effects" (["first", "second", "combine"], ((n, n + 1), (2 * (n + 1), 1))) (run n)
    , testGroup
        "ArrowChoice"
        [ testProperty "only the selected branch runs with its captured variable" $ do
            let select = A.Kleisli (["select"],)
                left = A.Kleisli (\(x, n) -> (["left"], x + n))
                right = A.Kleisli (\(b, m) -> (["right"], bool (negate m) m b))
                run :: ((Either Int Bool, Int), Int) -> ([String], Int)
                run = A.runKleisli (choiceT select left right)
            expect "left context" (["select", "left"], 13) (run ((Left 3, 10), 100))
            expect "right context" (["select", "right"], 100) (run ((Right True, 10), 100))
            expect "right payload" (["select", "right"], -100) (run ((Right False, 10), 100))
        , testProperty "pure injections preserve the preceding effect" $ do
            let left :: Int -> ([String], Either Int Bool)
                left = A.runKleisli (injectLeftT (A.Kleisli (["left input"],)))
                right :: Bool -> ([String], Either Int Bool)
                right = A.runKleisli (injectRightT (A.Kleisli (["right input"],)))
            expect "left injection" (["left input"], Left 3) (left 3)
            expect "right injection" (["right input"], Right True) (right True)
        ]
    , testGroup
        "ArrowLoop"
        [ testProperty "lazy feedback preserves surrounding effects and runs the body once" $ do
            n <- genNamed @Int "input"
            let before = A.Kleisli (\x -> (["before"], x + 1))
                body = A.Kleisli (\(x, u) -> (["loop"], (sum (take 3 u), x : u)))
                after = A.Kleisli (\x -> (["after"], x - 2))
                run :: Int -> ([String], Int)
                run = A.runKleisli (arrowLoopT before body after)
            expect "feedback and effects" (["before", "loop", "after"], 3 * (n + 1) - 2) (run n)
        , testProperty "recursive do preserves surrounding effects and runs the body once" $ do
            n <- genNamed @Int "input"
            let before = A.Kleisli (\x -> (["before"], x + 1))
                body = A.Kleisli (\(x, u) -> (["rec"], (sum (take 3 u), x : u)))
                after = A.Kleisli (\x -> (["after"], x - 2))
                run :: Int -> ([String], Int)
                run = A.runKleisli (arrowRecT before body after)
            expect "recursive feedback and effects" (["before", "rec", "after"], 3 * (n + 1) - 2) (run n)
        , testProperty "recursive do copies feedback values and discards unused outputs" $ do
            n <- genNamed @Int "input"
            let copyBody = A.Kleisli (\(x, u) -> (["copy"], (take 2 u, x : u)))
                dropBody = A.Kleisli (\(x, u) -> (["discard"], (x, x : u)))
                runCopy :: Int -> ([String], ([Int], [Int]))
                runCopy = A.runKleisli (arrowRecCopyT copyBody)
                runDrop :: Int -> ([String], [Int])
                runDrop = A.runKleisli (arrowRecDropT dropBody)
                runDiscard :: Int -> ([String], ())
                runDiscard = A.runKleisli (arrowRecDiscardT (A.Kleisli (["unused"],)) (A.Kleisli (\x -> ([show x], ()))))
            expect "feedback also used afterwards" (["copy"], (replicate 2 n, replicate 3 n)) (runCopy n)
            expect "unused output" (["discard"], replicate 3 n) (runDrop n)
            expect "no feedback or used outputs" (["unused", show n], ()) (runDiscard n)
        ]
    , testGroup
        "Star MonadFix"
        [ testProperty "loop and recursive do tie lazy feedback and preserve effect order" $ do
            n <- genNamed @Int "input"
            let before x = (["before"], x + 1)
                body (x, u) = (["body"], (sum (take 3 u), x : u))
                after x = (["after"], x - 2)
                runLoop, runRec :: Int -> ([String], Int)
                runLoop = starLoopT before body after
                runRec = starRecT before body after
                expected = (["before", "body", "after"], 3 * (n + 1) - 2)
            expect "Star loop" expected (runLoop n)
            expect "Star recursive do" expected (runRec n)
        ]
    , testGroup
        "FinRel"
        [ testProperty "application of a lifted exponential agrees with uncurrying" $ do
            f <- genNamed @((F2 ** F3) ~> F4) "f"
            let curried = Closed.curry @_ @F2 @F3 @F4 f
                actual = toSMC @(F F2 :** F F3) @(F F4) \(x, y) -> (curried -< x) SMC.! y
            expect "apply lifted function" f actual
        , testProperty "arrow application assembles tensor inputs" $ do
            f <- genNamed @(F2 ~> F3) "f"
            g <- genNamed @(F3 ~> F4) "g"
            let actual = toSMC @(F F2 :** F F3) @(F (F3 ** F4)) \(x, y) ->
                  (f ** g) -< (x, y)
            expect "tensor application" (f ** g) actual
            expect "term application" f (toSMC1 (\x -> f -< x))
            let pipeline = toSMC1 \x -> SMC.do
                  y <- f -< x
                  z <- liftF g y
                  returnA -< z
            expect "inferred intermediate result" (g . f) pipeline
        , testProperty "arrow application binds tensor results" $ do
            f <- genNamed @(F2 ~> (F2 ** F3)) "f"
            g <- genNamed @(F2 ~> F4) "g"
            h <- genNamed @(F3 ~> F2) "h"
            let actual = toSMC1 \z -> SMC.do
                  (x, y) <- f -< z
                  u <- g -< x
                  v <- h -< y
                  returnA -< (u, v)
            expect "process both components" ((g ** h) . f) actual
        , testProperty "matrix multiplication is composition (2, 3, 4)" $ do
            f <- genNamed @(F2 ~> F3) "f"
            g <- genNamed @(F3 ~> F4) "g"
            check "differs from g . f" (matMulT f g == g . f)
        , testProperty "the trace is the cap after the cup (3)" $ do
            f <- genNamed @(F3 ~> F3) "f"
            check "differs" (traceIdxT f == cap @F3 . (f ** obj @F3) . cup @F3)
        , testProperty "the entrywise product is mappend after the two after comult (2, 3)" $ do
            f <- genNamed @(F2 ~> F3) "f"
            g <- genNamed @(F2 ~> F3) "g"
            check "differs" (hadamardT f g == mappend @F3 . (f ** g) . comult @F2)
        , testProperty "an index used twice from a sum is the cup (3)" $
            check "differs from cup" (toSMC @I (\() -> sumOver @(F F3) \j -> j SMC.** j) == cup @F3)
        , testProperty "an unused summed index is the counit after the unit (3)" $
            check "differs" (toSMC @I (\() -> sumOver @(F F3) \_ -> unit) == counit @F3 . mempty @F3)
        , testProperty "einsum ij,jk->ik is composition (2, 3, 4)" $ do
            f <- genNamed @(F2 ~> F3) "f"
            g <- genNamed @(F3 ~> F4) "g"
            check "differs from g . f" (unStr (einsum @"ij,jk->ik" (name f) (name g)) == unStr (name (g . f)))
        ]
    , testGroup
        "Mat Int"
        [ testProperty "embedded unit results act as scalars on either side" $ do
            s <- genNamed @((Unit :: MatK Int) ~> Unit) "scalar"
            f <- genNamed @(M2 ~> M3) "f"
            let left = toSMC1 \x -> (s -< unit) *^ (f -< x)
                right = toSMC1 \x -> (f -< x) ^* (s -< unit)
            expect "left scalar" (unMat (leftUnitor . (s ** f) . leftUnitorInv)) (unMat left)
            expect "right scalar" (unMat (rightUnitor . (f ** s) . rightUnitorInv)) (unMat right)
        , testProperty "matrix multiplication is composition (2, 3, 2)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            g <- genNamed @(M3 ~> M2) "g"
            check "differs from g . f" (unMat (matMulT f g) == unMat (g . f))
        , testProperty "the trace is the sum of the diagonal (3)" $ do
            f <- genNamed @(M3 ~> M3) "f"
            check "differs from cap . (f ** id) . cup" (unMat (traceIdxT f) == unMat (cap @M3 . (f ** obj @M3) . cup @M3))
        , testProperty "the trace of the identity is the dimension (3)" $
            check "not 3" (unMat (traceIdxT (obj @M3)) == ((3 ::: VNil) ::: VNil))
        , testProperty "the transpose is the dagger (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            check "differs from dagger" (unMat (transposeT f) == unMat (dagger f))
        , testProperty "the entrywise product is mappend after the two after comult (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            g <- genNamed @(M2 ~> M3) "g"
            check "differs" (unMat (hadamardT f g) == unMat (mappend @M3 . (f ** g) . comult @M2))
        ]
    , testGroup
        "einsum on Mat Int"
        [ testProperty "ij,jk->ik is composition (2, 3, 2)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            g <- genNamed @(M3 ~> M2) "g"
            check "differs from g . f" (unMat (unStr (einsum @"ij,jk->ik" (name f) (name g))) == unMat (unStr (name (g . f))))
        , testProperty "ij->ji is the dagger (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            check "differs from dagger" (unMat (unStr (einsum @"ij->ji" (name f))) == unMat (unStr (name (dagger f))))
        , testProperty "ii-> is the trace (3)" $ do
            f <- genNamed @(M3 ~> M3) "f"
            check "differs" (unMat (unStr (einsum @"ii->" (name f))) == unMat (traceIdxT f))
        , testProperty "ij-> is the sum of the entries (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            check "differs" (unMat (unStr (einsum @"ij->" (name f))) == unMat (counit @M3 . f . mempty @M2))
        , testProperty "ij,ij->ij is the entrywise product (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            g <- genNamed @(M2 ~> M3) "g"
            check "differs" (unMat (unStr (einsum @"ij,ij->ij" (name f) (name g))) == unMat (unStr (name (hadamardT f g))))
        , testProperty "without ->, ij,jk is composition, at the type EinsumType computes (2, 3, 2)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            g <- genNamed @(M3 ~> M2) "g"
            check "differs" (unMat (unStr (matMulE (name f) (name g))) == unMat (unStr (name (g . f))))
        , testProperty "without ->, ji is the dagger, its output being sorted (2, 3)" $ do
            f <- genNamed @(M2 ~> M3) "f"
            check "differs from dagger" (unMat (unStr (einsum @"ji" (name f))) == unMat (unStr (name (dagger f))))
        , testProperty "without ->, ii is the trace (3)" $ do
            f <- genNamed @(M3 ~> M3) "f"
            check "differs" (unMat (unStr (einsum @"ii" (name f))) == unMat (traceIdxT f))
        , testProperty "i->ii puts a vector on the diagonal (3)" $ do
            u <- genNamed @(Unit ~> M3) "u"
            check "differs from comult" (unMat (unStr (einsum @"i->ii" (Str u :: Tensor '[M3]))) == unMat (comult @M3 . u))
        , testProperty "i,j->ij is the tensor of the two (2, 3)" $ do
            u <- genNamed @(Unit ~> M2) "u"
            v <- genNamed @(Unit ~> M3) "v"
            check
              "differs"
              (unMat (unStr (einsum @"i,j->ij" (Str u :: Tensor '[M2]) (Str v :: Tensor '[M3]))) == unMat ((u ** v) . leftUnitorInv))
        , testProperty "ijk->kij moves the last index to the front (2, 3)" $ do
            t <- genNamed @(Unit ~> Fold '[M2, M3, M2]) "t"
            check "differs from the reference" $
              entries (unStr (einsum @"ijk->kij" (Str t :: Tensor '[M2, M3, M2])))
                == reference [("ijk", [2, 3, 2], entries t)] "kij"
        , testProperty "ijk,jl->ljk contracts and reorders (2, 3)" $ do
            t <- genNamed @(Unit ~> Fold '[M2, M3, M2]) "t"
            u <- genNamed @(Unit ~> Fold '[M3, M2]) "u"
            check "differs from the reference" $
              entries (unStr (einsum @"ijk,jl->ljk" (Str t :: Tensor '[M2, M3, M2]) (Str u :: Tensor '[M3, M2])))
                == reference [("ijk", [2, 3, 2], entries t), ("jl", [3, 2], entries u)] "ljk"
        , testProperty "ij,jk,ki-> is the trace of the product of three (2)" $ do
            t <- genNamed @(Unit ~> Fold '[M2, M2]) "t"
            u <- genNamed @(Unit ~> Fold '[M2, M2]) "u"
            v <- genNamed @(Unit ~> Fold '[M2, M2]) "v"
            check "differs from the reference" $
              entries
                (unStr (einsum @"ij,jk,ki->" (Str t :: Tensor '[M2, M2]) (Str u :: Tensor '[M2, M2]) (Str v :: Tensor '[M2, M2])))
                == reference [("ij", [2, 2], entries t), ("jk", [2, 2], entries u), ("ki", [2, 2], entries v)] ""
        , testProperty "kl,jkk,ijx,li->li: a ring, a diagonal, an index of one tensor, three-legged spiders (2, 3)" $ do
            t <- genNamed @(Unit ~> Fold '[M2, M3]) "t"
            u <- genNamed @(Unit ~> Fold '[M3, M2, M2]) "u"
            v <- genNamed @(Unit ~> Fold '[M2, M3, M3]) "v"
            w <- genNamed @(Unit ~> Fold '[M3, M2]) "w"
            check "differs from the reference" $
              entries
                ( unStr
                    ( einsum @"kl,jkk,ijx,li->li"
                        (Str t :: Tensor '[M2, M3])
                        (Str u :: Tensor '[M3, M2, M2])
                        (Str v :: Tensor '[M2, M3, M3])
                        (Str w :: Tensor '[M3, M2])
                    )
                )
                == reference
                  [ ("kl", [2, 3], entries t)
                  , ("jkk", [3, 2, 2], entries u)
                  , ("ijx", [2, 3, 3], entries v)
                  , ("li", [3, 2], entries w)
                  ]
                  "li"
        , testProperty "ab,bc,xy,yz,cz->ax: two pairs contracted apart, then joined (2, 3)" $ do
            t <- genNamed @(Unit ~> Fold '[M2, M3]) "t"
            u <- genNamed @(Unit ~> Fold '[M3, M2]) "u"
            v <- genNamed @(Unit ~> Fold '[M3, M2]) "v"
            w <- genNamed @(Unit ~> Fold '[M2, M3]) "w"
            x <- genNamed @(Unit ~> Fold '[M2, M3]) "x"
            check "differs from the reference" $
              entries
                ( unStr
                    ( einsum @"ab,bc,xy,yz,cz->ax"
                        (Str t :: Tensor '[M2, M3])
                        (Str u :: Tensor '[M3, M2])
                        (Str v :: Tensor '[M3, M2])
                        (Str w :: Tensor '[M2, M3])
                        (Str x :: Tensor '[M2, M3])
                    )
                )
                == reference
                  [ ("ab", [2, 3], entries t)
                  , ("bc", [3, 2], entries u)
                  , ("xy", [3, 2], entries v)
                  , ("yz", [2, 3], entries w)
                  , ("cz", [2, 3], entries x)
                  ]
                  "ax"
        , testPropertyWith fewer "ij,jk,kl,lm->im is the product of four (3)" $ do
            t <- genNamed @(Unit ~> Fold '[M3, M3]) "t"
            u <- genNamed @(Unit ~> Fold '[M3, M3]) "u"
            v <- genNamed @(Unit ~> Fold '[M3, M3]) "v"
            w <- genNamed @(Unit ~> Fold '[M3, M3]) "w"
            check "differs from the reference" $
              entries
                ( unStr
                    ( einsum @"ij,jk,kl,lm->im"
                        (Str t :: Tensor '[M3, M3])
                        (Str u :: Tensor '[M3, M3])
                        (Str v :: Tensor '[M3, M3])
                        (Str w :: Tensor '[M3, M3])
                    )
                )
                == reference
                  [("ij", [3, 3], entries t), ("jk", [3, 3], entries u), ("kl", [3, 3], entries v), ("lm", [3, 3], entries w)]
                  "im"
        , testProperty "ijk->ijki copies an index to a later position (2, 3)" $ do
            t <- genNamed @(Unit ~> Fold '[M2, M3, M2]) "t"
            check "differs from the reference" $
              entries (unStr (einsum @"ijk->ijki" (Str t :: Tensor '[M2, M3, M2])))
                == reference [("ijk", [2, 3, 2], entries t)] "ijki"
        ]
    ]
  where
    -- the product of all four would have 6561 entries; contracting pairwise keeps it at 81
    fewer = defaultTestOptions{overrideNumTests = Just 5}

-- | The entries of a state of Mat, the first index varying fastest.
entries :: Mat (a :: MatK Int) b -> [Int]
entries (Mat m) = concatMap toList m

-- | Einstein summation on tensors given by their letters, the sizes of their indices and their
-- entries, the first index varying fastest, written out as sums of products.
reference :: [(String, [Int], [Int])] -> String -> [Int]
reference ins out =
  [ bool
      0
      (sum [product [at dims vs (pick ls) | (ls, dims, vs) <- ins] | rest <- tuples restDims, let pick = assign rest])
      consistent
  | o <- tuples (fmap size out)
  , let fixed = M.fromListWith (\a b -> bool (-1) a (a == b)) (zip out o)
        consistent = (-1) `notElem` M.elems fixed
        assign rest ls = [M.findWithDefault (M.fromList (zip summed rest) M.! l) l fixed | l <- ls]
  ]
  where
    size l = sum (take 1 [d | (ls, dims, _) <- ins, (l', d) <- zip ls dims, l' == l])
    summed = nubOrd [l | (ls, _, _) <- ins, l <- ls, l `notElem` out]
    restDims = fmap size summed
    -- every index tuple, the first index varying fastest
    tuples ds = fmap reverse (traverse (\d -> [0 .. d - 1]) (reverse ds))
    at dims vs is = vs !! foldr (\(d, i) acc -> i + d * acc) 0 (zip dims is)
