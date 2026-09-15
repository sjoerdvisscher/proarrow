{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Relations and weighted graphs on a bare set of points, given as a table: a list of edges with
-- their weights in the enriching category @v@. 'Edges' is an enriched profunctor on the discrete
-- category of an 'Indexed' kind -- over a discrete base there is nothing to be compatible with -- so
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

-- | The edge list, reflected to the value level.
type EdgeList :: forall {k} {v}. [(k, k, v)] -> Kind
data EdgeList es where
  ENil :: EdgeList '[]
  ECons :: forall x y w es. (KnownIndex x, KnownIndex y, Ob w) => EdgeList es -> EdgeList ('(x, y, w) ': es)

type KnownEdges :: forall {k} {v}. [(k, k, v)] -> Constraint
class KnownEdges es where
  edges :: EdgeList es
instance KnownEdges '[] where
  edges = ENil
instance (KnownIndex x, KnownIndex y, Ob w, KnownEdges es) => KnownEdges ('(x, y, w) ': es) where
  edges = ECons edges

-- | A graph with 'BOOL' weights is a relation on the points: decided by walking the edge list.
instance (Indexed k, KnownEdges es) => ThinProfunctor (Edges (es :: [(k, k, BOOL)]))

instance (Indexed k, KnownEdges es) => DecidableProfunctor (Edges (es :: [(k, k, BOOL)])) where
  type Holds (Edges es) a b = WeightOf es a b
  decide @a @b = go (edges @es)
    where
      go
        :: forall (es' :: [(k, k, BOOL)])
         . (WeightOf es' a b ~ WeightOf es a b)
        => EdgeList es' -> Decision (Edges es) a b (WeightOf es' a b)
      go ENil = No
      go (ECons @x @y @w es') = case (decideEq @a @(D x), decideEq @b @(D y)) of
        (Yes Eq.Refl, Yes Eq.Refl) -> case obj @w of
          Tru -> Yes Edge
          Fls -> No
        (No, _) -> go es'
        (Yes _, No) -> go es'
  toHolds Edge r = r

-- | The weight of a pair, reflected to the value level by walking the edge list.
withObWeight
  :: forall {k} {v} (es :: [(k, k, v)]) a b r
   . (Quantale v, Indexed k, KnownEdges es, KnownIndex a, KnownIndex b)
  => ((Ob (WeightOf es a b)) => r) -> r
withObWeight r = go (edges @es) r
  where
    go :: forall (es' :: [(k, k, v)]). EdgeList es' -> ((Ob (WeightOf es' a b)) => r) -> r
    go ENil r' = r'
    go (ECons @x @y es') r' = case (decideEq @a @(D x), decideEq @b @(D y)) of
      (Yes Eq.Refl, Yes Eq.Refl) -> r'
      (No, _) -> go es' r'
      (Yes _, No) -> go es' r'

-- | A unit into a weight is an edge at the unit, since an object above the unit is the unit.
enrichedEdge
  :: forall {k} {v} (es :: [(k, k, v)]) a b
   . (Quantale v, Indexed k, KnownEdges es, KnownIndex a, KnownIndex b)
  => Unit ~> WeightOf es a b -> Edges es a b
enrichedEdge f = go (edges @es) f
  where
    go
      :: forall (es' :: [(k, k, v)])
       . (WeightOf es' a b ~ WeightOf es a b)
      => EdgeList es' -> Unit ~> WeightOf es' a b -> Edges es a b
    go ENil g = unitIsNotBottom @v g
    go (ECons @x @y @w es') g = case (decideEq @a @(D x), decideEq @b @(D y)) of
      (Yes Eq.Refl, Yes Eq.Refl) -> unitIsTop @v @w g Edge
      (No, _) -> go es' g
      (Yes _, No) -> go es' g

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
