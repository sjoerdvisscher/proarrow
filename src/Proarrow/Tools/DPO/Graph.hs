-- | Classical double-pushout rewriting of directed multigraphs.
module Proarrow.Tools.DPO.Graph
  ( Graph (..)
  , GraphHom (..)
  , pushoutGraph
  , GraphRule (..)
  , pushoutComplementGraph
  , dpoStepGraph
  ) where

import Data.Map.Strict qualified as M
import Data.Set qualified as Set
import Data.Universe.Class (Finite (..))
import Prelude qualified as P

import Proarrow.Core (CategoryOf (..))
import Proarrow.Category.Instance.FinHask (FH, FinHask (..))
import Proarrow.Colimit.Pushout (pushout)
import Proarrow.Tools.DPO (pushoutComplement)

-- | A finite directed multigraph: a vertex type @v@, an edge type @e@, and the incidence
-- functions @src, tgt :: e -> v@.
data Graph v e = Graph
  { graphSrc :: FH e ~> FH v
  , graphTgt :: FH e ~> FH v
  }

-- | A graph homomorphism: a pair of functions on vertices and edges. Well-formedness
-- (commuting with @src@/@tgt@) is a precondition of the functions below, not checked here —
-- the same convention 'Proarrow.Colimit.Pushout' uses for its own square-commutativity.
data GraphHom v1 e1 v2 e2 = GraphHom
  { vertexMap :: FH v1 ~> FH v2
  , edgeMap :: FH e1 ~> FH e2
  }

-- | The pushout of two graph homomorphisms sharing a domain: vertices and edges are pushed
-- out independently in @FINHASK@ (graph colimits, like all presheaf colimits, are computed
-- pointwise), and the incidence functions of the result are induced from the two input
-- graphs' incidence functions.
pushoutGraph
  :: forall vA eA vB eB vI eI ans
   . Graph vA eA
  -> Graph vB eB
  -> GraphHom vI eI vA eA
  -> GraphHom vI eI vB eB
  -> (forall vH eH. Graph vH eH -> GraphHom vA eA vH eH -> GraphHom vB eB vH eH -> ans)
  -> ans
pushoutGraph a b (GraphHom vLegA eLegA) (GraphHom vLegB eLegB) ok =
  pushout vLegA vLegB \vA2vH@(FinHask vA2vHMap) vB2vH@(FinHask vB2vHMap) ->
    pushout eLegA eLegB \eA2eH@(FinHask eA2eHMap) eB2eH@(FinHask eB2eHMap) ->
      let
        -- every edge of a pushout has a preimage in A or B, since pushouts in Set are jointly surjective
        fromA = M.fromList [(h, e) | (e, h) <- M.toList eA2eHMap]
        fromB = M.fromList [(h, e) | (e, h) <- M.toList eB2eHMap]
        indexOf (FinHask fA) (FinHask fB) h = case M.lookup h fromA of
          P.Just e -> vA2vHMap M.! (fA M.! e)
          P.Nothing -> case M.lookup h fromB of
            P.Just e -> vB2vHMap M.! (fB M.! e)
            P.Nothing -> P.error "pushoutGraph: every edge of a pushout has a preimage"
        hSrc = FinHask (M.fromList [(h, indexOf (graphSrc a) (graphSrc b) h) | h <- universeF])
        hTgt = FinHask (M.fromList [(h, indexOf (graphTgt a) (graphTgt b) h) | h <- universeF])
      in
        ok (Graph hSrc hTgt) (GraphHom vA2vH eA2eH) (GraphHom vB2vH eB2eH)

-- | A graph rewrite rule: a span @L \<- K -> R@ of graph homomorphisms, together with @R@
-- itself (needed, since gluing @R@ into the result requires @R@'s own incidence functions).
data GraphRule vK eK vL eL vR eR = GraphRule
  { ruleLeft :: GraphHom vK eK vL eL
  , ruleRight :: GraphHom vK eK vR eR
  , ruleR :: Graph vR eR
  }

-- | Compute the pushout complement of a rule's left leg and a match into a host graph @g@.
-- Fails (calls the second continuation) if the gluing condition doesn't hold: either an
-- identification conflict (as in plain 'Proarrow.Category.Instance.FinHask.FINHASK', on
-- vertices or on edges), or the graph-specific /dangling condition/ — an edge that survives
-- the rewrite is still attached to a vertex that the rewrite deletes.
pushoutComplementGraph
  :: forall vK eK vL eL vG eG ans
   . Graph vG eG
  -> GraphHom vK eK vL eL
  -> GraphHom vL eL vG eG
  -> (forall vD eD. Graph vD eD -> GraphHom vK eK vD eD -> GraphHom vD eD vG eG -> ans)
  -> ans
  -> ans
pushoutComplementGraph g (GraphHom vLeft eLeft) (GraphHom vMatch eMatch) ok notGlueable =
  pushoutComplement
    vLeft
    vMatch
    ( \vK2vD vD2vG@(FinHask vD2vGMap) ->
        pushoutComplement
          eLeft
          eMatch
          ( \eK2eD eD2eG@(FinHask eD2eGMap) ->
              let
                vertexImage = Set.fromList (M.elems vD2vGMap)
                endpointsSurvive eg =
                  Set.member (unFinHask (graphSrc g) M.! eg) vertexImage
                    P.&& Set.member (unFinHask (graphTgt g) M.! eg) vertexImage
              in
                if P.not (P.all endpointsSurvive (M.elems eD2eGMap))
                  then notGlueable
                  else
                    let
                      vG2vD = M.fromList [(v, k) | (k, v) <- M.toList vD2vGMap]
                      dSrc = FinHask (P.fmap (\eg -> vG2vD M.! (unFinHask (graphSrc g) M.! eg)) eD2eGMap)
                      dTgt = FinHask (P.fmap (\eg -> vG2vD M.! (unFinHask (graphTgt g) M.! eg)) eD2eGMap)
                    in
                      ok (Graph dSrc dTgt) (GraphHom vK2vD eK2eD) (GraphHom vD2vG eD2eG)
          )
          notGlueable
    )
    notGlueable

-- | Apply a 'GraphRule' to a host graph at a match @L -> G@. On success, the continuation
-- receives the rewrite's cospan legs @D -> G@, @D -> H@ and the embedding @R -> H@ of the
-- newly created pattern into the result @H@ (given explicitly, since unlike a bare object in
-- a kind-indexed category, a 'Graph' carries data the caller needs to keep rewriting).
--
-- ==== Example: deleting an edge
--
-- The host graph @g@ is a single edge between two vertices:
--
-- >  g:   0 --e0--> 1
--
-- The rule deletes that edge but keeps both endpoints: @L@ has the edge, @K@ and @R@ don't.
--
-- >  L:   0 --e--> 1        K:   0   1        R:   0   1
--
-- Matching @L@'s edge @e@ onto @g@'s @e0@ and applying the rule keeps both vertices (tracked
-- by @r2h@, the embedding of @R@ into the result) and leaves no edges behind:
--
-- >>> import Proarrow.Category.Instance.FinHask (Fin, fromList, toList)
-- >>> import Proarrow.Core ((\\))
-- >>> let g = Graph (fromList [(0 :: Fin 1, 0 :: Fin 2)]) (fromList [(0 :: Fin 1, 1 :: Fin 2)]) :: Graph (Fin 2) (Fin 1)
-- >>> let k = Graph (fromList []) (fromList []) :: Graph (Fin 2) (Fin 0)
-- >>> let idV = fromList [(0 :: Fin 2, 0 :: Fin 2), (1 :: Fin 2, 1 :: Fin 2)]
-- >>> let rule = GraphRule (GraphHom idV (fromList [])) (GraphHom idV (fromList [])) k :: GraphRule (Fin 2) (Fin 0) (Fin 2) (Fin 1) (Fin 2) (Fin 0)
-- >>> let m = GraphHom idV (fromList [(0 :: Fin 1, 0 :: Fin 1)]) :: GraphHom (Fin 2) (Fin 1) (Fin 2) (Fin 1)
-- >>> (dpoStepGraph g rule m (\h _ _ r2h -> (P.show (toList (vertexMap r2h), toList (graphSrc h), toList (graphTgt h))) \\ graphSrc h) "gluing failed") :: P.String
-- "([(0,0),(1,1)],[],[])"
--
-- ==== Example: the dangling condition
--
-- Same host graph @g@, but the rule instead deletes vertex @0@ in isolation: @L@ has one
-- vertex and no edges, @K@ and @R@ are empty.
--
-- >  L:   0                 K:   (empty)       R:   (empty)
--
-- Vertex @0@ still has @e0@ attached to it in @g@, and @e0@ isn't part of the match, so
-- deleting the vertex would leave @e0@ dangling — the gluing condition fails:
--
-- >>> let k' = Graph (fromList []) (fromList []) :: Graph (Fin 0) (Fin 0)
-- >>> let rule' = GraphRule (GraphHom (fromList []) (fromList [])) (GraphHom (fromList []) (fromList [])) k' :: GraphRule (Fin 0) (Fin 0) (Fin 1) (Fin 0) (Fin 0) (Fin 0)
-- >>> let m' = GraphHom (fromList [(0 :: Fin 1, 0 :: Fin 2)]) (fromList []) :: GraphHom (Fin 1) (Fin 0) (Fin 2) (Fin 1)
-- >>> dpoStepGraph g rule' m' (\_ _ _ _ -> "glued (unexpected)") "gluing failed"
-- "gluing failed"
dpoStepGraph
  :: forall vK eK vL eL vR eR vG eG ans
   . Graph vG eG
  -> GraphRule vK eK vL eL vR eR
  -> GraphHom vL eL vG eG
  -> (forall vD eD vH eH. Graph vH eH -> GraphHom vD eD vG eG -> GraphHom vD eD vH eH -> GraphHom vR eR vH eH -> ans)
  -> ans
  -> ans
dpoStepGraph g (GraphRule left right r) m ok notGlueable =
  pushoutComplementGraph
    g
    left
    m
    (\d k2d d2g -> pushoutGraph d r k2d right \h d2h r2h -> ok h d2g d2h r2h)
    notGlueable
