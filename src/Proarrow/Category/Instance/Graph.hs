module Proarrow.Category.Instance.Graph where

import Prelude (type (~))

import Proarrow.Category.Enriched.Thin (ThinProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, lmap, type (+->), Hom)
import Proarrow.Profunctor.Direpresentable (Direp)
import Proarrow.Profunctor.Representable (Rep)

type data GRAPH (p :: k +-> j) = GR j k
type family GrJ a where
  GrJ (GR j k) = j
type family GrK a where
  GrK (GR j k) = k

data Graph a b where
  Graph :: (HasArrow p aj ak, HasArrow p bj bk) => aj ~> bj -> ak ~> bk -> Graph (GR aj ak :: GRAPH p) (GR bj bk)
instance (ThinProfunctor p) => Profunctor (Graph :: CAT (GRAPH p)) where
  dimap = dimapDefault
  r \\ Graph f g = r \\ f \\ g
instance (ThinProfunctor p) => Promonad (Graph :: CAT (GRAPH p)) where
  id = Graph id id
  Graph f1 g1 . Graph f2 g2 = Graph (f1 . f2) (g1 . g2)

-- | The graph of a thin profunctor. Doing this for any profunctor would need dependent types.
instance (ThinProfunctor p) => CategoryOf (GRAPH p) where
  type (~>) = Graph
  type Ob @(GRAPH p) ab = (ab ~ GR (GrJ ab) (GrK ab), Ob (GrJ ab), Ob (GrK ab), HasArrow p (GrJ ab) (GrK ab))

-- | A morphism gives two equal ways to compute the "diagonal", which is an element of the profunctor.
diagonalElement
  :: forall {j} {k} (p :: k +-> j) (aj :: j) (ak :: k) (bj :: j) (bk :: k) r
   . (ThinProfunctor p) => GR aj ak ~> (GR bj bk :: GRAPH p) -> ((HasArrow p aj bk) => r) -> r
diagonalElement (Graph f g) = withArr @p @aj @bk (lmap f (arr @p @bj @bk) \\ f \\ g)

-- | The arrow category is the graph of the hom-functor. Here we require the category to be thin.
type ARROW k = GRAPH (Hom k)

-- | The category of elements of a functor.
type ELEMENTS f = GRAPH (Rep f)

-- | The comma category f/g is the graph of @C(f(-), g(=))@.
type f `COMMA` g = GRAPH (Direp f g)