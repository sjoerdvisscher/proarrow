{-# LANGUAGE AllowAmbiguousTypes #-}

-- | __The schema of directed graphs__: the two-object category @E ⇉ V@, worked out in full. A
-- copresheaf on it is a graph, a profunctor @'GRAPH' '+->' k@ is a diagram of graphs shaped like
-- @k@, and both are finitary whenever the sets are. Small as it is, it is a complete example of
-- standing up a finite category: the arrows, the object enumeration, the numbering of the hom-sets
-- that makes it a 'Proarrow.Category.Enriched.Finitary.FiniteCat', and the instances that make it
-- testable. "Props.Finitary.Graph" and "Props.DPO" are what it is put to work for.
module Examples.Graph where

import Data.List (genericIndex, genericLength)
import Data.Type.Nat (SNat (..), snat)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Finitary (Finitary (..))
import Proarrow.Category.Enriched.Thin (Enumerable (..), Finite (..), Indexed (..))
import Proarrow.Core (CAT, CategoryOf (..), ObId (..), Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Testing
  ( GenTotal (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow
  , genSomeFinite
  , optGen
  )
import Proarrow.Testing.Laws (testCategory, testFinitary)

-- | Two objects: the edges and the vertices.
type data GRAPH = E | V

-- | Four morphisms: the two identities, and an edge's source and target.
type GraphHom :: CAT GRAPH
data GraphHom a b where
  IdE :: GraphHom E E
  IdV :: GraphHom V V
  Src :: GraphHom E V
  Tgt :: GraphHom E V

deriving instance Eq (GraphHom a b)
deriving instance Show (GraphHom a b)

instance ObId E where objId = IdE
instance ObId V where objId = IdV

instance CategoryOf GRAPH where
  type (~>) = GraphHom

instance Profunctor GraphHom where
  dimap = dimapDefault
  r \\ f = case f of IdE -> r; IdV -> r; Src -> r; Tgt -> r

instance Promonad GraphHom where
  g . IdE = g
  IdV . f = f

instance Indexed GRAPH
instance Finite GRAPH where type Objects GRAPH = '[E, V]
instance Enumerable GRAPH where
  withIndex @a r = case obj @a of
    IdE -> r
    IdV -> r
  withOb @a r = case snat @(Index a) of
    SZ -> r
    SS @i -> case snat @i of SZ -> r

-- | The arrows of the schema, which is all the numbering needs: two identities and the two
-- incidence maps. Having finitely many of them is what lets the gluing conditions be enumerated.
graphHoms :: forall a b. (Ob a, Ob b) => [GraphHom a b]
graphHoms = case (obj @a, obj @b) of
  (IdE, IdE) -> [IdE]
  (IdV, IdV) -> [IdV]
  (IdE, IdV) -> [Src, Tgt]
  (IdV, IdE) -> []

instance Finitary GraphHom where
  size @a @b = genericLength (graphHoms @a @b)
  toIndex IdE = 0
  toIndex IdV = 0
  toIndex Src = 0
  toIndex Tgt = 1
  fromIndex @a @b i = graphHoms @a @b `genericIndex` i
  elements = graphHoms

-- * The schema as a testable category

instance TestingEqShow (GraphHom a b)

instance (Ob a, Ob b) => TestableType (GraphHom a b) where
  gen = case (obj @a, obj @b) of
    (IdE, IdE) -> optGen [IdE]
    (IdV, IdV) -> optGen [IdV]
    (IdE, IdV) -> optGen [Src, Tgt]
    (IdV, IdE) -> GenEmpty \case {}

instance TestableProfunctor GraphHom

instance Testable GRAPH where
  showOb @a = case obj @a of IdE -> "E"; IdV -> "V"
  genSome = genSomeFinite

test :: TestTree
test =
  testGroup
    "Graph"
    [ testCategory @GRAPH
    , -- the numbering of the hom-sets, which everything finitary over this schema is built on
      testFinitary @GraphHom "GraphHom"
    ]
