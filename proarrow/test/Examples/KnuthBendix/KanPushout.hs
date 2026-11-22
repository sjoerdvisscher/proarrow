-- | A pushout of finite sets computed as a left Kan extension. The source
-- category is a span Common -> LeftSet, Common -> RightSet. Its inclusion
-- into the commuting square adds Apex, where the extension is the pushout.
--
-- Tags from a fresh Root name the elements of the three input sets.
-- Naturality moves those tags along the span's functions. Commutativity of
-- the square then identifies their two images at Apex. Unlike a group action,
-- these arrows cannot be cancelled: input elements remain distinct even when
-- their images in the pushout coincide.
module Examples.KnuthBendix.KanPushout (test, SpanGenerator (..), Element, spanCompletion, leftImage, rightImage, apexImages) where

import Data.Fin (Fin, fin0, fin1, universe)
import Data.Kind (Type)
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat, Nat0, Nat1, Nat2, Nat3)
import Data.Vec.Lazy (Vec (..))
import Data.Vec.Lazy qualified as V
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths, path)
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT)
import Proarrow.Testing (check, expect)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.Laws (ProEquation ((:=:)))

data Root
data Common
data LeftSet
data RightSet
data Apex

type SpanGenerator :: Nat -> CAT Type
data SpanGenerator n a b where
  ToLeft :: SpanGenerator n Common LeftSet
  ToRight :: SpanGenerator n Common RightSet
  MergeLeft :: SpanGenerator n LeftSet Apex
  MergeRight :: SpanGenerator n RightSet Apex
  SourceTag :: Fin n -> SpanGenerator n Root Common
  LeftTag :: Fin Nat2 -> SpanGenerator n Root LeftSet
  RightTag :: Fin Nat2 -> SpanGenerator n Root RightSet

deriving instance Show (SpanGenerator n a b)

instance EqGen (SpanGenerator n) where
  eqGen ToLeft ToLeft = Just Refl
  eqGen ToRight ToRight = Just Refl
  eqGen MergeLeft MergeLeft = Just Refl
  eqGen MergeRight MergeRight = Just Refl
  eqGen (SourceTag a) (SourceTag b) | a == b = Just Refl
  eqGen (LeftTag a) (LeftTag b) | a == b = Just Refl
  eqGen (RightTag a) (RightTag b) | a == b = Just Refl
  eqGen _ _ = Nothing

type Element :: Nat -> Type
type Element n = Paths (PTH Root :: PATHS (SpanGenerator n)) (PTH Apex)

-- The input sets LeftSet and RightSet both have two elements. The common
-- set has n elements, and the two FinSet arrows supply their tag equations.
spanCompletion
  :: FinSet (FS n) (FS Nat2) -> FinSet (FS n) (FS Nat2) -> KB.Completion (SpanGenerator n)
spanCompletion (FinSet f) (FinSet g) =
  KB.complete (KB.Limits 100 2000) $
    (path MergeLeft ToLeft :=: path MergeRight ToRight)
      : concat
        [ [ path ToLeft (SourceTag i) :=: path (LeftTag (f V.! i))
          , path ToRight (SourceTag i) :=: path (RightTag (g V.! i))
          ]
        | i <- universe
        ]

-- Images of a, b from LeftSet and c, d from RightSet, in that order.
apexImages :: KB.System (SpanGenerator n) -> [Element n]
apexImages system = map (leftImage system) [fin0, fin1] ++ map (rightImage system) [fin0, fin1]

leftImage :: KB.System (SpanGenerator n) -> Fin Nat2 -> Element n
leftImage system i = KB.normalise system (path MergeLeft (LeftTag i))

rightImage :: KB.System (SpanGenerator n) -> Fin Nat2 -> Element n
rightImage system i = KB.normalise system (path MergeRight (RightTag i))

-- Compare kernels of the two maps from LeftSet + RightSet. This establishes
-- the same quotient without relying on either algorithm's representative order.
samePartition
  :: KB.System (SpanGenerator n) -> FinSet (FS n) (FS Nat2) -> FinSet (FS n) (FS Nat2) -> Bool
samePartition system f g = pushout f g \(FinSet l) (FinSet r) ->
  let pairs = zip (V.toList l ++ V.toList r) (apexImages system)
  in and [(x == y) == (p == q) | (x, p) <- pairs, (y, q) <- pairs]

test :: TestTree
test =
  testGroup
    "Pushout as a Kan extension"
    [ testProperty "one shared point identifies a with c" $ do
        let f :: FinSet (FS Nat1) (FS Nat2)
            f = FinSet (fin0 ::: VNil)
        system <- case spanCompletion f f of
          KB.Complete s -> pure s
          KB.Incomplete reason _ _ -> testFailed (show reason)
        let images = apexImages system
        expect "three apex elements" 3 (S.size (S.fromList (map show images)))
        expect "a and c have the same image" (leftImage system fin0) (rightImage system fin0)
        check "same quotient as the existing pushout" (samePartition system f f)
    , testProperty "an empty common set gives the disjoint union" $ do
        let f :: FinSet (FS Nat0) (FS Nat2)
            f = FinSet VNil
        system <- case spanCompletion f f of
          KB.Complete s -> pure s
          KB.Incomplete reason _ _ -> testFailed (show reason)
        expect "four apex elements" 4 (S.size (S.fromList (map show (apexImages system))))
        check "same quotient as the existing pushout" (samePartition system f f)
    , testProperty "all spans from three points agree with the finite-set pushout" $ do
        let maps :: [FinSet (FS Nat3) (FS Nat2)]
            maps = [FinSet (a ::: b ::: c ::: VNil) | a <- [fin0, fin1], b <- [fin0, fin1], c <- [fin0, fin1]]
        mapM_
          ( \(f, g) -> do
              system <- case spanCompletion f g of
                KB.Complete s -> pure s
                KB.Incomplete reason _ _ -> testFailed (show (f, g) ++ ": " ++ show reason)
              check ("different identifications for " ++ show (f, g)) (samePartition system f g)
          )
          [(f, g) | f <- maps, g <- maps]
    , testProperty "identifying apex elements does not identify input elements" $ do
        let f :: FinSet (FS Nat3) (FS Nat2)
            f = FinSet (fin0 ::: fin0 ::: fin1 ::: VNil)
            g = FinSet (fin0 ::: fin1 ::: fin1 ::: VNil)
        system <- case spanCompletion f g of
          KB.Complete s -> pure s
          KB.Incomplete reason _ _ -> testFailed (show reason)
        expect "all four apex images coincide" 1 (S.size (S.fromList (map show (apexImages system))))
        let source = [show (KB.normalise system (path (SourceTag i))) | i <- universe @Nat3]
            left = [show (KB.normalise system (path (LeftTag i))) | i <- [fin0, fin1]]
            right = [show (KB.normalise system (path (RightTag i))) | i <- [fin0, fin1]]
        expect "three distinct common elements" 3 (S.size (S.fromList source))
        expect "two distinct left elements" 2 (S.size (S.fromList left))
        expect "two distinct right elements" 2 (S.size (S.fromList right))
    ]
