{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Relations and weighted graphs on a bare set of points, given as a table: a list of edges with
-- their weights in the enriching category @v@. 'Edges' is an enriched profunctor on the discrete
-- category of an 'Indexed' kind (over a discrete base there is nothing to be compatible with), so
-- it composes, and its Kleene closure 'Proarrow.Category.Enriched.Thin.Composition.Closure' is
-- reachability for 'BOOL' weights and shortest paths for 'COST' weights.
module Proarrow.Profunctor.Instance.Edges where

import Data.Kind (Constraint)
import Data.Type.Equality qualified as Eq
import Prelude (type (~))

import Proarrow.Category.Enriched (EnrichedProfunctor (..))
import Proarrow.Category.Enriched.Quantale (Quantale (..))
import Proarrow.Category.Enriched.Thin
  ( DecidableProfunctor (..)
  , Decision (..)
  , Equal
  , Indexed
  , KnownIndex
  , ThinProfunctor
  , decideEq
  )
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), If)
import Proarrow.Category.Instance.Cost (COST)
import Proarrow.Category.Instance.Discrete (DISCRETE (..), Discrete (..), deltaAct)
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Kind, Profunctor (..), obj, type (+->))
import Proarrow.Limit.BinaryProduct (type (&&))
import Proarrow.Object (KnownListOf (..), ListOf (..))

-- | A weighted graph on the bare set of points of an 'Indexed' kind, given as a list of edges with
-- their weights in @v@: an enriched profunctor on the discrete category, since over a discrete base
-- there is nothing to be compatible with. Unlisted pairs are at 'InitialObject', a pair listed twice
-- takes its first weight, and an element is a pair at 'Unit' weight.
type Edges :: forall {k} {v}. [(k, k, v)] -> DISCRETE k +-> DISCRETE k
data Edges es a b where
  Edge :: (Ob a, Ob b, WeightOf es a b ~ Unit) => Edges es a b

type WeightOf :: forall {k} {v}. [(k, k, v)] -> DISCRETE k -> DISCRETE k -> v
type family WeightOf es a b where
  WeightOf '[] a b = InitialObject
  WeightOf ('(x, y, w) ': es) a b = If (Equal a (D x) && Equal b (D y)) w (WeightOf es a b)

instance (Indexed k) => Profunctor (Edges (es :: [(k, k, v)])) where
  dimap Refl Refl e = e
  r \\ Edge = r

-- | The source of an edge.
type EdgeSrc :: forall {k} {v}. (k, k, v) -> k
type family EdgeSrc e where
  EdgeSrc '(x, y, w) = x

-- | The target of an edge.
type EdgeTgt :: forall {k} {v}. (k, k, v) -> k
type family EdgeTgt e where
  EdgeTgt '(x, y, w) = y

-- | The weight of an edge.
type EdgeWeight :: forall {k} {v}. (k, k, v) -> v
type family EdgeWeight e where
  EdgeWeight '(x, y, w) = w

-- | An edge whose endpoints are known and whose weight is an object.
type KnownEdge :: forall {k} {v}. (k, k, v) -> Constraint
class
  (e ~ '(EdgeSrc e, EdgeTgt e, EdgeWeight e), KnownIndex (EdgeSrc e), KnownIndex (EdgeTgt e), Ob (EdgeWeight e)) =>
  KnownEdge e

instance
  (e ~ '(EdgeSrc e, EdgeTgt e, EdgeWeight e), KnownIndex (EdgeSrc e), KnownIndex (EdgeTgt e), Ob (EdgeWeight e))
  => KnownEdge e

-- | The edge list, reflected to the value level.
type EdgeList :: forall k v. [(k, k, v)] -> Kind
type EdgeList @k @v = ListOf (KnownEdge :: (k, k, v) -> Constraint)

type KnownEdges :: forall {k} {v}. [(k, k, v)] -> Constraint
type KnownEdges es = KnownListOf KnownEdge es

-- | The weight of a pair, found by walking the edge list: the first continuation when the pair is
-- not listed, the second with the weight when it is.
lookupEdge
  :: forall {k} {v} (es :: [(k, k, v)]) a b r
   . (Indexed k, KnownIndex a, KnownIndex b)
  => EdgeList es
  -> ((WeightOf es a b ~ InitialObject) => r)
  -> (forall w. (WeightOf es a b ~ w, Ob w) => r)
  -> r
lookupEdge Nil none _ = none
lookupEdge (Cons @'(x, y, w) es) none found = case (decideEq @a @(D x), decideEq @b @(D y)) of
  (Yes Eq.Refl, Yes Eq.Refl) -> found @w
  (No, _) -> lookupEdge @_ @a @b es none found
  (Yes _, No) -> lookupEdge @_ @a @b es none found

-- | A graph with 'BOOL' weights is a relation on the points: decided by walking the edge list.
instance (Indexed k, KnownEdges es) => ThinProfunctor (Edges (es :: [(k, k, BOOL)]))

instance (Indexed k, KnownEdges es) => DecidableProfunctor (Edges (es :: [(k, k, BOOL)])) where
  type Holds (Edges es) a b = WeightOf es a b
  decide @a @b = lookupEdge @es @a @b listOf No \ @w -> case obj @w of
    Tru -> Yes Edge
    Fls -> No
  toHolds Edge r = r

-- | The weight of a pair, reflected to the value level by walking the edge list.
withObWeight
  :: forall {k} {v} (es :: [(k, k, v)]) a b r
   . (Quantale v, Indexed k, KnownEdges es, KnownIndex a, KnownIndex b)
  => ((Ob (WeightOf es a b)) => r) -> r
withObWeight r = lookupEdge @es @a @b listOf r r

-- | A unit into a weight is an edge at the unit, since an object above the unit is the unit.
enrichedEdge
  :: forall {k} {v} (es :: [(k, k, v)]) a b
   . (Quantale v, Indexed k, KnownEdges es, KnownIndex a, KnownIndex b)
  => Unit ~> WeightOf es a b -> Edges es a b
enrichedEdge f = lookupEdge @es @a @b listOf (unitIsNotBottom @v f) \ @w -> unitIsTop @v @w f Edge

-- | A graph with 'COST' weights: a weighted graph, whose closure is shortest paths.
instance (Indexed k, KnownEdges es) => EnrichedProfunctor COST (Edges (es :: [(k, k, COST)])) where
  type ProObj COST (Edges es) a b = WeightOf es a b
  withProObj @a @b = withObWeight @es @a @b
  underlying Edge = obj @(Unit :: COST)
  enriched @a @b = enrichedEdge @es @a @b
  rmap @a @b @c =
    withObWeight @es @a @b (withObWeight @es @a @c (deltaAct @b @c @(WeightOf es a b) @(WeightOf es a c) Eq.Refl))
  lmap @a @b @c =
    withObWeight @es @a @b (withObWeight @es @c @b (deltaAct @c @a @(WeightOf es a b) @(WeightOf es c b) Eq.Refl))
