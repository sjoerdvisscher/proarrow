{-# LANGUAGE QualifiedDo #-}

-- | Index notation in "Proarrow.Tools.SMC", checked against the structure of the category: in
-- 'FinRel', where a sum over an index is "there is", and in 'Mat' over 'Int', where it is a sum of
-- numbers.
module Props.SMC (test, name) where

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
import Proarrow.Category.Monoidal.Hypergraph (Hypergraph, cap, cup)
import Proarrow.Category.Monoidal.Strictified (Fold, Strictified (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj, (\\))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Testing (check, genNamed)
import Proarrow.Testing.Laws (defaultTestOptions)
import Proarrow.Tools.Einsum (EinsumType, Tensor, einsum)
import Proarrow.Tools.SMC (SYN (..), delta, lift, sumOver, toSMC, unit, (*^))
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
transposeT f = toSMC @(F M3) \j -> sumOver @(F M2) \i -> delta (lift f i) j *^ i

-- | A morphism as a tensor with an index for its input and one for its output.
name :: forall {k} (a :: k) b. (Hypergraph k) => a ~> b -> Tensor '[a, b]
name f = Str ((obj @a ** f) . cup @a) \\ f

-- | Matrix multiplication at the type 'EinsumType' computes, which is checked by compiling it.
matMulE :: EinsumType "ij,jk" '[ '[M2, M3], '[M3, M2]]
matMulE = einsum @"ij,jk"

-- `\_ -> unit` binds a summed index that is not used, which is what is tested.
{- HLINT ignore test "Use const" -}
test :: TestTree
test =
  testGroup
    "SMC"
    [ testGroup
        "FinRel"
        [ testProperty "matrix multiplication is composition (2, 3, 4)" $ do
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
        [ testProperty "matrix multiplication is composition (2, 3, 2)" $ do
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
  [ if consistent
      then sum [product [at dims vs (pick ls) | (ls, dims, vs) <- ins] | rest <- tuples restDims, let pick = assign rest]
      else 0
  | o <- tuples (fmap size out)
  , let fixed = M.fromListWith (\a b -> if a == b then a else -1) (zip out o)
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
