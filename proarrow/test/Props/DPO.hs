{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Double-pushout rewriting of directed graphs, done entirely with the generic machinery: a graph
-- is a finitary copresheaf on the two-object schema @E ⇉ V@, built from ordinary runtime data by
-- 'withSubobject' out of an ambient graph, and rewritten by 'dpoStep'. Nothing here is about graphs
-- except the schema and the ambient object; the pushouts, the pushout complement and both halves of
-- the gluing condition all come from the generic @FINITARY GRAPH ()@ instances.
module Props.DPO (test) where

import Data.List (genericIndex, genericLength)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (Property, testFailed, testProperty)
import Prelude hiding (id, (.))

import Examples.Graph (GRAPH (..), GraphHom (..))
import Proarrow.Category.Enriched.Finitary (Finitary (..))
import Proarrow.Category.Enriched.Finitary.Topos (FIN, withSubobject)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (Sub (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj)
import Proarrow.Functor (Copresheaf)
import Proarrow.Limit.Equalizer (factorEqualizer)
import Proarrow.Testing (expect)
import Proarrow.Tools.DPO (Rule (..), dpoStep)

-- * An ambient graph to carve subgraphs out of

data Node = N0 | N1 | N2
  deriving (Enum, Eq, Ord, Show)

nodes :: [Node]
nodes = [N0, N1, N2]

-- | Every node, and one edge for each ordered pair of them. Every simple digraph on at most three
-- vertices is a subobject of this, which is how one gets built from runtime data.
type Ambient :: Copresheaf GRAPH
data Ambient u b where
  Vtx :: Node -> Ambient '() V
  Edg :: Node -> Node -> Ambient '() E

deriving instance Eq (Ambient u b)
deriving instance Show (Ambient u b)

instance Profunctor Ambient where
  dimap Unit IdE x = x
  dimap Unit IdV x = x
  dimap Unit Src (Edg s _) = Vtx s
  dimap Unit Tgt (Edg _ t) = Vtx t
  r \\ x = case x of Vtx{} -> r; Edg{} -> r

-- | The ambient graph's own elements, in the order the numbering below uses.
ambient :: forall b. (Ob b) => [Ambient '() b]
ambient = case obj @b of
  IdE -> [Edg s t | s <- nodes, t <- nodes]
  IdV -> [Vtx v | v <- nodes]

instance Finitary Ambient where
  size @_ @b = genericLength (ambient @b)
  toIndex (Vtx v) = fromIntegral (fromEnum v)
  toIndex (Edg s t) = fromIntegral (fromEnum s * length nodes + fromEnum t)
  fromIndex @_ @b i = ambient @b `genericIndex` i
  elements @_ @b = ambient @b

-- * Graphs as subobjects of it

-- | A subgraph of 'Ambient', given by its inclusion.
type Incl g = FIN g ~> FIN Ambient

-- | A graph given as a list of vertices and a list of edges. Rejects a list of edges whose endpoints
-- are not all listed, that being exactly what stops it from being a subgraph.
withGraph :: [Node] -> [(Node, Node)] -> (forall g. (Finitary g) => Incl g -> r) -> r -> r
withGraph vs es = withSubobject @Ambient \case
  Vtx v -> v `elem` vs
  Edg s t -> (s, t) `elem` es

-- | Read a graph back as its lists of vertices and edges, for comparison.
graphOf :: forall g. (Finitary (g :: Copresheaf GRAPH)) => Incl g -> ([Node], [(Node, Node)])
graphOf (Sub (Prof incl)) =
  ( [v | Vtx v <- map incl (elements @g @'() @V)]
  , [(s, t) | Edg s t <- map incl (elements @g @'() @E)]
  )

-- | Apply the rule that deletes everything of @l@ which is not in @k@, matched at @l@\'s inclusion
-- into the host @g@. Every graph is given by its inclusion into 'Ambient', and the maps between them
-- are the factorizations those inclusions force.
deleteStep
  :: forall (g :: Copresheaf GRAPH) (l :: Copresheaf GRAPH) (k :: Copresheaf GRAPH)
   . (Finitary g, Finitary l, Finitary k)
  => Incl g
  -> Incl l
  -> Incl k
  -> ((Natural, Natural) -> (Natural, Natural) -> Property ())
  -- ^ given the complement's and the result's counts of vertices and edges
  -> Property ()
  -> Property ()
deleteStep gIncl lIncl kIncl ok notGlueable =
  dpoStep
    (Rule (factorEqualizer lIncl kIncl) (id :: FIN k ~> FIN k))
    (factorEqualizer gIncl lIncl)
    ( \(Sub (Prof @d _)) _ (Sub (Prof @_ @h _)) ->
        ok (size @d @'() @V, size @d @'() @E) (size @h @'() @V, size @h @'() @E)
    )
    notGlueable

-- | The host, the matched part and the interface, each as a list of vertices and a list of edges.
rewrite
  :: ([Node], [(Node, Node)])
  -> ([Node], [(Node, Node)])
  -> ([Node], [(Node, Node)])
  -> ((Natural, Natural) -> (Natural, Natural) -> Property ())
  -> Property ()
  -> Property ()
rewrite (gv, ge) (lv, le) (kv, ke) ok notGlueable =
  withGraph
    gv
    ge
    (\g -> withGraph lv le (\l -> withGraph kv ke (\k -> deleteStep g l k ok notGlueable) notSub) notSub)
    notSub

-- | What the edge-deleting rule should leave behind: both vertices and no edge, in the complement
-- and in the result alike.
edgeGone :: (Natural, Natural) -> (Natural, Natural) -> Property ()
edgeGone d h = do
  expect "the complement keeps both vertices and no edge" (2, 0) d
  expect "and so does the result" (2, 0) h

notSub :: Property ()
notSub = testFailed "should have been a subgraph"

-- | A single edge between two vertices, the host of both rewriting examples.
host :: ([Node], [(Node, Node)])
host = ([N0, N1], [(N0, N1)])

test :: TestTree
test =
  testGroup
    "DPO"
    [ testProperty "a graph from runtime data is a subgraph of the ambient one" $
        withGraph [N0, N1] [(N0, N1)] (\incl -> expect "one edge, two vertices" host (graphOf incl)) notSub
    , testProperty "an edge whose endpoints are missing is not a subgraph" $
        withGraph [N0] [(N0, N1)] (\_ -> testFailed "should not have been a subgraph") (pure ())
    , testProperty "deleting an edge keeps its endpoints" $
        -- the classical example: L is the edge with both endpoints, K and R are the endpoints alone
        rewrite host host ([N0, N1], []) edgeGone (testFailed "should have been glueable")
    , testProperty "deleting a vertex that still has an edge is refused" $
        -- the dangling condition: L is vertex N0 alone, so the edge N0->N1 would be left hanging
        rewrite host ([N0], []) ([], []) (\_ _ -> testFailed "should not have glued") (pure ())
    ]
