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
import Proarrow.Category.Sheaf
  ( Coverage
  , Factors (..)
  , HasFiniteCovers (..)
  , PulledBack (..)
  , Site (..)
  , SomeCover (..)
  , SomeLeg (..)
  , StableSite (..)
  , pullbackAlongId
  )
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
-- incidence maps. Since there are finitely many, the gluing conditions can be enumerated.
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

-- * A coverage on the schema

-- | A coverage on the graph schema @E ⇉ V@: the vertex 'V' is covered by the two ends of an edge,
-- the arrows 'Src' and 'Tgt' out of 'E'. Most sites in this repo are posets, with at most one
-- arrow between two objects. Here the legs are parallel, so a sieve at 'V' (a set of arrows
-- into 'V' closed under precomposition) can hold 'Src' without 'Tgt', and a factorisation through
-- a leg can be well typed and still wrong. That gives 'Proarrow.Testing.Laws.testStableSite'
-- something to check.
--
-- It is a Grothendieck topology: the only arrows into 'V' are its identity and the two legs, so a
-- cover pulls back either to itself or to the identity cover of 'E'. It is also
-- 'Proarrow.Category.Sheaf.ByImage' of the inclusion of 'E', written out because the schema reads
-- better as itself.
--
-- A sheaf for it is a presheaf with @p 'V' ≅ p 'E' × p 'E'@. The legs do not overlap (nothing but
-- 'E' maps into 'E'), so matching is vacuous and gluing is a product. For overlapping legs see
-- @Props.Sheaf@\'s @Overlapping@, on a poset.
type ByEnds :: Coverage
type data ByEnds

-- | The name of 'ByEnds'\'s one cover, whose 'Cover' constructor is @VByEnds@ and whose 'Leg'
-- constructors are @AtSrc@ and @AtTgt@.
type data Endpoints

instance Site ByEnds GRAPH where
  data Cover ByEnds GRAPH a c where
    VByEnds :: Cover ByEnds GRAPH V Endpoints
  data Leg ByEnds GRAPH a c x where
    AtSrc :: Leg ByEnds GRAPH V Endpoints E
    AtTgt :: Leg ByEnds GRAPH V Endpoints E
  legArrow AtSrc = Src
  legArrow AtTgt = Tgt
  legs VByEnds = [SomeLeg AtSrc, SomeLeg AtTgt]

instance HasFiniteCovers ByEnds GRAPH where
  covers @a = case obj @a of
    IdE -> []
    IdV -> [SomeCover VByEnds]

-- | Each leg is its own pullback along itself, and the cover pulls back to itself along the
-- identity. @'Factors' AtTgt IdE@ type-checks where @'Factors' AtSrc IdE@ is meant, since the legs
-- share a source, so unlike on a poset these equations are the instance's to get right.
instance StableSite ByEnds GRAPH where
  pullbackCover VByEnds IdV = pullbackAlongId VByEnds
  pullbackCover VByEnds Src = AlreadyFactors (Factors AtSrc IdE)
  pullbackCover VByEnds Tgt = AlreadyFactors (Factors AtTgt IdE)

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
