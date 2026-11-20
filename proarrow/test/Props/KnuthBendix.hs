module Props.KnuthBendix (test) where

import Data.List (sort)
import Data.Type.Equality ((:~:) (..))
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (Word)

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..))
import Proarrow.Core (CAT)
import Proarrow.Testing (check, expect)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.Laws qualified as Laws

type Letter :: CAT ()
data Letter a b where
  Letter :: Char -> Letter '() '()
deriving instance Show (Letter a b)

instance EqGen Letter where
  eqGen (Letter a) (Letter b) = if a == b then Just Refl else Nothing

type Word = Paths (PTH '() :: PATHS Letter) (PTH '())

word :: String -> Word
word = foldr (\c -> PCons (Letter c)) PNil

letters :: Paths (a :: PATHS Letter) b -> String
letters PNil = ""
letters (PCons (Letter c) rest) = c : letters rest

rank :: Letter a b -> Char
rank (Letter c) = c

presentation :: [(String, String)] -> [KB.Equation Letter]
presentation = map (\(a, b) -> word a KB.:=: word b)

finished :: [(String, String)] -> Either String (KB.System Letter)
finished eqs = case KB.completeWithOrder rank (KB.Limits 100 2000) (presentation eqs) of
  KB.Complete system -> Right system
  KB.Incomplete reason _ _ -> Left (show reason)

partial :: [(String, String)] -> KB.System Letter
partial eqs = case KB.completeWithOrder rank (KB.Limits 100 (length eqs)) (presentation eqs) of
  KB.Complete system -> system
  KB.Incomplete _ system _ -> system

-- Shared regression cases for completion invariants and both normalisers.
presentations :: [[(String, String)]]
presentations =
  [ [("ab", "d"), ("d", "c")]
  , [("abc", "d"), ("ab", "e")]
  , [("aa", "b")]
  , [("ab", ""), ("bc", "d")]
  , [("ab", "d"), ("bc", "e")]
  , [("zy", "ab"), ("bc", "d")]
  , [("abc", "d"), ("b", "a")]
  , [("xb", "a"), ("zz", "xc"), ("c", "b")]
  , [("ab", ""), ("zc", "d")]
  , []
  ]

wordsUpTo :: Int -> String -> [String]
wordsUpTo 0 _ = [""]
wordsUpTo n alphabet = "" : [c : w | c <- alphabet, w <- wordsUpTo (n - 1) alphabet]

ruleWords :: KB.System Letter -> [(String, String)]
ruleWords system = [KB.withRule r (\a b -> (letters a, letters b)) | r <- KB.rules system]

reductions :: KB.System Letter -> [String]
reductions system = [a ++ " -> " ++ b | (a, b) <- ruleWords system]

steps :: [(String, String)] -> String -> [String]
steps rs w =
  [ take i w ++ rhs ++ drop (i + length lhs) w
  | (lhs, rhs) <- rs
  , i <- [0 .. length w - length lhs]
  , take (length lhs) (drop i w) == lhs
  ]

referenceNormal :: [(String, String)] -> String -> String
referenceNormal rs w = case steps rs w of
  [] -> w
  next : _ -> referenceNormal rs next

interreduced :: KB.System Letter -> Bool
interreduced system =
  let rs = ruleWords system
  in and [null (steps (take i rs ++ drop (i + 1) rs) l) && null (steps rs r) | (i, (l, r)) <- zip [0 ..] rs]

allJoined :: KB.System Letter -> Bool
allJoined system = all (\(a, b) -> KB.equivalent system (word a) (word b)) (wordPairs (ruleWords system))

-- Independent string oracle: try every ordered pair and every nonempty cut.
wordPairs :: [(String, String)] -> [(String, String)]
wordPairs rs =
  [ (a, b)
  | (l, r) <- rs
  , (l', r') <- rs
  , i <- [0 .. length l - 1]
  , let suffix = drop i l
        shared = min (length suffix) (length l')
  , shared > 0
  , take shared suffix == take shared l'
  , let a = r ++ drop (length suffix) l'
        b = take i l ++ r' ++ drop (length l') suffix
  , a /= b
  ]

test :: TestTree
test =
  testGroup
    "Coloured Knuth-Bendix"
    [ testProperty "default ordering uses first appearance and custom ordering can override it" $ do
        automatic <- case KB.complete (KB.Limits 10 100) (presentation [("b", "a")]) of
          KB.Complete system -> pure system
          KB.Incomplete reason _ _ -> testFailed (show reason)
        custom <- either testFailed pure (finished [("b", "a")])
        expect "first appearance puts b before a" ["a -> b"] (reductions automatic)
        expect "custom alphabet puts a before b" ["b -> a"] (reductions custom)
    , testProperty "default systems preserve generators absent from their presentation" $ do
        system <- case KB.complete (KB.Limits 10 100) (presentation [("ab", "")]) of
          KB.Complete result -> pure result
          KB.Incomplete reason _ _ -> testFailed (show reason)
        expect "unseen context is preserved" "zz" (letters (KB.normalise system (word "zabz")))
        check "unseen generators stay distinct" (not (KB.equivalent system (word "y") (word "z")))
        check "a known generator differs from an unseen one" (not (KB.equivalent system (word "a") (word "z")))
        case KB.complete (KB.Limits 0 0) [] of
          KB.Complete empty -> do
            expect "empty alphabet leaves paths alone" "zabz" (letters (KB.normalise empty (word "zabz")))
            check "empty alphabet preserves distinctions" (not (KB.equivalent empty (word "y") (word "z")))
          _ -> testFailed "empty presentation did not complete"
    , testProperty "crossing overlaps add the missing word rule" $ do
        system <- either testFailed pure (finished [("ab", "d"), ("bc", "e")])
        check "derived crossing equation" ("dc -> ae" `elem` reductions system)
        expect "both branches normalise together" "ae" (letters (KB.normalise system (word "dc")))
    , testProperty "inclusion overlaps are completed too" $ do
        system <- either testFailed pure (finished [("abc", "d"), ("b", "a")])
        check "long rule after inclusion" ("aac -> d" `elem` reductions system)
        check "equation preserved" (KB.equivalent system (word "abc") (word "d"))
    , testProperty "proper self-overlaps are processed" $ do
        system <- either testFailed pure (finished [("aa", "b")])
        check "self-overlap exists" (length (KB.rules system) > 1)
        check "the two reductions of aaa agree" (KB.equivalent system (word "ba") (word "ab"))
    , testProperty "indexed overlaps agree with exhaustive string overlaps" $ do
        let examples =
              [ [("ab", "d"), ("bc", "e"), ("xy", "z")]
              , [("aba", "c"), ("aca", "d"), ("ba", "e")]
              , [("abc", "d"), ("b", "a"), ("aa", "e")]
              ]
        mapM_
          ( \es -> do
              let system = partial es
                  actual = [Laws.withSides e (\a b -> (letters a, letters b)) | e <- KB.criticalPairs system]
              expect "missing or duplicated overlap" (sort (wordPairs (ruleWords system))) (sort actual)
          )
          (examples ++ presentations)
    , testProperty "identity replacements expose new boundary matches" $ do
        system <- either testFailed pure (finished [("ab", ""), ("bc", "d")])
        expect "empty replacement" "" (letters (KB.normalise system (word "abab")))
        check "crossing through cancellation" (KB.equivalent system (word "c") (word "ad"))
    , testProperty "incremental replacement normalises surrounding boundaries" $ do
        boundary <- either testFailed pure (finished [("zy", "ab"), ("bc", "d")])
        expect "replacement meets normal tail" "ad" (letters (KB.normalise boundary (word "zyc")))
        deletion <- either testFailed pure (finished [("ab", ""), ("zc", "d")])
        expect "deletion joins both contexts" "d" (letters (KB.normalise deletion (word "zabc")))
    , testProperty "compiled matching agrees on reductions, boundaries and unseen generators" $ do
        let inputs = ["zyc", "zabc", "xyzzy", "!ab!", "~aa~"] ++ wordsUpTo 3 "abcdez"
        mapM_
          ( \es -> do
              system <- either testFailed pure (finished es)
              automatic <- case KB.complete (KB.Limits 100 2000) (presentation es) of
                KB.Complete s -> pure s
                KB.Incomplete reason _ _ -> testFailed (show reason)
              let agrees current =
                    let compiled = KB.compile rank current
                        same w =
                          let expected = KB.normalise current (word w)
                              incremental = foldr (\c -> KB.rewriteCompiled compiled (Letter c)) PNil w
                          in KB.normaliseCompiled compiled (word w) == expected && incremental == expected
                    in all same inputs
                  automaticAgrees w =
                    let expected = referenceNormal (ruleWords automatic) w
                        incremental = foldr (\c -> KB.rewrite automatic (Letter c)) PNil w
                    in letters (KB.normalise automatic (word w)) == expected && letters incremental == expected
              check "compiled normal form differs" (all agrees [system, partial es])
              check "automatic dispatch differs from string rewriting" (all automaticAgrees inputs)
          )
          presentations
    , testProperty "completed rules have irreducible left sides and normal right sides" $ do
        systems <- traverse (either testFailed pure . finished) presentations
        check "a rule can still be simplified" (all interreduced systems)
        check "an overlap was lost" (all allJoined systems)
        check
          "an input equation was lost"
          (and [KB.equivalent system (word a) (word b) | (system, eqs) <- zip systems presentations, (a, b) <- eqs])
    , testProperty "collapse retains its equation when a completion limit interrupts" $ do
        let es = presentation [("abc", "d"), ("ab", "e")]
            remaining = map (\e -> Laws.withSides e (\a b -> letters a ++ " = " ++ letters b))
            checkPending system pending = do
              expect "obsolete rule removed" ["ab -> e"] (reductions system)
              expect "collapsed equation retained" ["ec = d"] (remaining pending)
        case KB.completeWithOrder rank (KB.Limits 10 2) es of
          KB.Incomplete KB.EquationLimit system pending -> checkPending system pending
          _ -> testFailed "equation limit discarded the collapsed rule"
        case KB.completeWithOrder rank (KB.Limits 1 100) es of
          KB.Incomplete KB.RuleLimit system pending -> checkPending system pending
          _ -> testFailed "rule limit did not account for the removed rule"
    , testProperty "shortlex orients equal lengths and cannot orient an empty left side" $ do
        system <- either testFailed pure (finished [("", "aa"), ("b", "a")])
        expect "strictly decreasing rules" ["b -> a", "aa -> "] (reductions system)
        expect "constant-size reduction" "a" (letters (KB.normalise system (word "b")))
        check "all critical pairs join" (allJoined system)
    , testProperty "limits retain obligations and never report completion prematurely" $ do
        case KB.completeWithOrder rank (KB.Limits 0 10) (presentation [("ab", "")]) of
          KB.Incomplete KB.RuleLimit system pending -> do
            expect "no rules" 0 (length (KB.rules system))
            expect "pending initial equation" 1 (length pending)
          _ -> testFailed "rule limit was ignored"
        case KB.completeWithOrder rank (KB.Limits 10 2) (presentation [("ab", "d"), ("bc", "e")]) of
          KB.Incomplete KB.EquationLimit system pending -> do
            expect "two processed equations" 2 (length (KB.rules system))
            check "pending equations" (not (null pending))
          _ -> testFailed "equation limit was ignored"
        case KB.completeWithOrder rank (KB.Limits 0 0) [] of
          KB.Complete system -> expect "empty presentation" 0 (length (KB.rules system))
          _ -> testFailed "an empty presentation needs no budget"
    , testProperty "exhaustive short words have one reachable irreducible result" $ do
        let eqs = [("ab", "d"), ("bc", "e")]
        system <- either testFailed pure (finished eqs)
        let rs = ruleWords system
            normalForms w = case steps rs w of [] -> [w]; next -> concatMap normalForms next
            agrees w =
              let whole = letters (KB.normalise system (word w))
                  incremental = letters (foldr (\c -> KB.rewrite system (Letter c)) PNil w)
              in all (== whole) (normalForms w) && incremental == whole
        check "strategy-dependent normal form" (all agrees (wordsUpTo 4 "abcde"))
    ]
