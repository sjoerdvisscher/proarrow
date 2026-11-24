-- | Rewriting of open hypergraphs, modulo Frobenius wiring, with individual
-- rules or a compiled discrimination net sharing matching work across rules.
-- A rule's common boundary is the interface retained when replacing its left side.
-- Fixed-pattern matches are injective on nodes and box occurrences. The left boundary must also
-- be injective; the right boundary may join interface nodes. This is a restricted
-- DPO rewriting operation, not a general pushout-complement search for DPOI.
--
-- See "Proarrow.Tools.HypergraphRewrite.Completion" for Knuth–Bendix-style
-- completion and "Proarrow.Tools.HypergraphRewrite.Laws" for rule construction
-- from categorical laws.
module Proarrow.Tools.HypergraphRewrite
  ( -- * Rules
    Rule
  , rule
  , (==>)
  , Parameter (Literal, Variable)
  , mapParameter
  , parameterRule
  , subgraphRule
  , withSortParameters
  , Port (..)
  , PortGraph (..)
  , portRule
  , parameterPortRule
  , parameterPortRuleWith

    -- * Rewriting
  , rewrites
  , rewriteBatch
  , CompiledRules
  , compileRules
  , compileReducingRules
  , rewritesCompiled
  , rewriteBatchCompiled

    -- * Normalisation
  , RewriteLimits (..)
  , unlimitedRewrites
  , NormalisationStatus (..)
  , NormalisationResult (..)
  , normalise
  ) where

import Data.Vector qualified as V
import Prelude

import Proarrow.Category.Instance.OpenHypergraph (OPENHG, WireSorts, Wires, unsafeOpenHypergraph)
import Proarrow.Core (CategoryOf (..), (//))
import Proarrow.Optic.Iso (DecidableIso)
import Proarrow.Tools.HypergraphRewrite.Internal
  ( Graph (..)
  , NormalisationResult (..)
  , NormalisationStatus (..)
  , Parameter (Literal, Variable)
  , Port (..)
  , PortGraph (..)
  , Prepared
  , RewriteLimits (..)
  , Rule (..)
  , deletedImages
  , graph
  , mapParameter
  , matches
  , nonConflictingBy
  , normaliseBy
  , parameterPortRule
  , parameterPortRuleWith
  , parameterRule
  , portRule
  , replaceMany
  , replaceSelected
  , rule
  , subgraphRule
  , unlimitedRewrites
  , withSortParameters
  )
import Proarrow.Tools.HypergraphRewrite.Internal.Matcher (CompiledRules (..), compileRuleSet, compiledMatches)

infix 1 ==>

-- | An oriented rule written left to right. This checks the same boundary
-- conditions as 'rule'.
(==>) :: (a :: OPENHG s l) ~> b -> a ~> b -> Either String (Rule s l)
(==>) = rule

-- | All valid single-step rewrites, in box and node enumeration order.
-- Works for closed hosts (empty boundaries) as well as open hosts. No result
-- deletes a node used by an unmatched box or the host boundary. Unmatched nodes,
-- including isolated nodes, are retained. Distinct matches may produce isomorphic results;
-- results are not deduplicated. Matching is a finite exhaustive search.
-- Compatible label/arity candidates are cached per pattern box, and mapped
-- ports constrain later boxes through incidence indices. Labels only need 'Eq'.
rewrites
  :: forall {s} l a b
   . (Eq l, DecidableIso s)
  => Rule s l
  -> (a :: OPENHG s l) ~> b
  -> [Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l)]
rewrites (Rule lhs instantiate) host =
  let g = graph host
  in host //
       [ unsafeOpenHypergraph nodes ins outs boxes
       | (match, labels) <- matches lhs g
       , Just rhs <- [instantiate labels]
       , let Graph nodes ins outs boxes = replaceMany lhs rhs g [match]
       ]
rewrites r host = map snd (rewritesCompiled (either error id (compileRules [((), r)])) host)

-- | Apply a greedy maximal set of non-conflicting matches of one rule from a
-- single host snapshot, rebuilding the graph once. Returns the number applied
-- and the result, or @(0, host)@ when the rule does not match.
--
-- Matches are considered in the same order as 'rewrites'. They may share
-- preserved interface nodes, including adjacent regions connected through those
-- nodes. They cannot share boxes, or delete a node used by another chosen match.
-- Each replacement gets fresh nodes and all interfaces are glued simultaneously.
-- This selects one maximal batch, not a maximum-size batch or all possible batches.
-- New matches created by replacement are left for a later batch.
rewriteBatch
  :: forall {s} l as bs
   . (Eq l, DecidableIso s)
  => Rule s l
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> (Int, Wires as ~> (Wires bs :: OPENHG s l))
rewriteBatch (Rule lhs instantiate) host =
  let g = graph host
      candidates = [(rhs, match) | (match, labels) <- matches lhs g, Just rhs <- [instantiate labels]]
      chosen = nonConflictingBy (\_ (m, _) -> deletedImages lhs m) candidates
  in case chosen of
       [] -> (0, host)
       _ ->
         host //
           let Graph nodes ins outs boxes = replaceSelected g [(lhs, rhs, match) | (rhs, match) <- chosen]
           in (length chosen, unsafeOpenHypergraph nodes ins outs boxes)
rewriteBatch r host = rewriteBatchCompiled (either error id (compileRules [((), r)])) host

-- | Compile uniquely keyed rules. Box traversal favours connected boxes and
-- then boxes with more fixed ports; fixed arity breaks ties.
-- This anchors a mux before its constant inputs and fixed edges before captures.
-- Common tests are inserted into a discrimination trie, including bindings for
-- isolated nodes and separate searches for disconnected pattern components.
-- Literal labels dispatch by equality; parameter labels dispatch by constructor
-- and fixed fields. Bindings are checked separately for each rule at a terminal.
-- Compilation also compares sorts up to isomorphism. Rules using
-- 'withSortParameters' defer sort validation to their terminals.
compileRules
  :: (Ord key, Eq l, DecidableIso s)
  => [(key, Rule s l)] -> Either String (CompiledRules key s l)
compileRules = compileRuleSet False

-- | Compile rules with a strictly decreasing box-count policy. A candidate is
-- accepted only when its instantiated replacement has fewer boxes than the
-- matched region. This check precedes batch selection, so a rejected candidate
-- cannot block a competing reduction. Parameters and dynamically constructed
-- replacements are checked per match; compilation does not certify that every
-- application of the supplied rules decreases.
--
-- Every application removes at least one box, and compatible batches cannot
-- share boxes. Consequently 'normalise' with 'unlimitedRewrites' terminates on
-- finite hosts after at most the initial number of boxes in rule applications,
-- assuming replacement callbacks terminate. Matching is still an exhaustive
-- finite search and may be expensive. Confluence is not guaranteed.
--
-- Equal-sized changes, including relabelling, and growing replacements are
-- excluded, even if semantically useful. 'NormalForm' means no decreasing
-- application remains; other applications of the original rules may exist.
--
-- >>> import Proarrow.Category.Instance.OpenHypergraph (Box (..))
-- >>> let before = unsafeOpenHypergraph [] [] [] [Box "x" [] []] :: (Wires '[] :: OPENHG () String) ~> Wires '[]
-- >>> let after = unsafeOpenHypergraph [] [] [] [] :: (Wires '[] :: OPENHG () String) ~> Wires '[]
-- >>> let r = either error id (before ==> after)
-- >>> let compiled = either error id (compileReducingRules [((), r)])
-- >>> let result = normalise unlimitedRewrites compiled before
-- >>> (normalisationStatus result, normalisationRewrites result)
-- (NormalForm,1)
compileReducingRules
  :: (Ord key, Eq l, DecidableIso s)
  => [(key, Rule s l)] -> Either String (CompiledRules key s l)
compileReducingRules = compileRuleSet True

-- | Enumerate every valid match of every compiled rule, returning its key and
-- single-step result. Results are ordered by key, then by the original rule's
-- box and node enumeration order, as in 'rewrites'. Matching work is shared;
-- overlapping matches and isomorphic results are retained.
rewritesCompiled
  :: forall {s} key l a b
   . (Eq l, DecidableIso s)
  => CompiledRules key s l
  -> (a :: OPENHG s l) ~> b
  -> [(key, Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l))]
rewritesCompiled compiled@(CompiledRules rules _ _ _) host =
  host //
    [ (key, unsafeOpenHypergraph ns ins outs bs)
    | (i, (lhs, rhs, match)) <- compiledMatches compiled g
    , let (key, _) = rules V.! i
          Graph ns ins outs bs = replaceMany lhs rhs g [match]
    ]
  where
    g = graph host

-- | Match the entire compiled rule set on one snapshot and apply one greedy
-- maximal batch across rules. Smaller keys have conflict priority; matches of
-- one rule follow 'rewrites' order. Compatible matches of different rules share
-- the batch and the result is rebuilt once. Sharing and deletion conditions are
-- the same as in 'rewriteBatch'. New matches wait for a subsequent batch.
rewriteBatchCompiled
  :: forall {s} key l as bs
   . (Eq l, DecidableIso s)
  => CompiledRules key s l
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> (Int, Wires as ~> (Wires bs :: OPENHG s l))
rewriteBatchCompiled compiled host =
  let g = graph host
      chosen = batchMatches compiled g
  in case chosen of
       [] -> (0, host)
       _ ->
         host //
           let Graph ns ins outs bs = replaceSelected g chosen
           in (length chosen, unsafeOpenHypergraph ns ins outs bs)

-- | Repeatedly apply compatible batches from the compiled rule set. Matches
-- created by one batch are considered on the next snapshot. Conflict priorities
-- are those of 'compileRules'. A rewrite limit can truncate a batch to its first
-- compatible matches, so neither limit is exceeded.
--
-- Stopping at a limit probes for further matches to distinguish exhaustion from
-- a normal form, without applying another rewrite. Ordinary rules do not compare
-- graphs: reproducing the left side still counts as an application and needs a
-- limit. Subgraph rules skip structurally identical replacements. Arbitrary
-- rule sets may not terminate with 'unlimitedRewrites';
-- 'compileReducingRules' excludes all non-decreasing applications.
normalise
  :: forall {s} key l as bs
   . (Eq l, DecidableIso s)
  => RewriteLimits
  -> CompiledRules key s l
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> NormalisationResult (Wires as ~> (Wires bs :: OPENHG s l))
normalise limits compiled = normaliseBy limits (batchMatches compiled)

batchMatches :: (Eq l, DecidableIso s) => CompiledRules key s l -> Graph s l -> [Prepared s l]
batchMatches compiled g =
  [ (lhs, rhs, match)
  | ((lhs, rhs), match) <-
      nonConflictingBy
        (\(lhs, _) (m, _) -> deletedImages lhs m)
        [((lhs, rhs), match) | (_, (lhs, rhs, match)) <- compiledMatches compiled g]
  ]
