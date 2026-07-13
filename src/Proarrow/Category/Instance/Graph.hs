module Proarrow.Category.Instance.Graph where

import Prelude (type (~))

import Proarrow.Category.Enriched.Thin (CodiscreteProfunctor, ThinProfunctor (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, lmap, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Optic (Iso', iso)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Direpresentable (Direp)
import Proarrow.Profunctor.Identity (Id)
import Proarrow.Profunctor.Representable (Rep (..))

type data GRAPH (p :: k +-> j) = GR j k

data family ProjJ :: forall (p :: k +-> j) -> GRAPH p +-> j
instance (ThinProfunctor p) => FunctorForRep (ProjJ p) where
  type (ProjJ p) @ GR x y = x
  fmap (Graph l _) = l

data family ProjK :: forall (p :: k +-> j) -> GRAPH p +-> k
instance (ThinProfunctor p) => FunctorForRep (ProjK p) where
  type (ProjK p) @ GR x y = y
  fmap (Graph _ r) = r

data Graph a b where
  Graph
    :: forall {p} aj ak bj bk
     . (HasArrow p aj ak, HasArrow p bj bk) => aj ~> bj -> ak ~> bk -> Graph (GR aj ak :: GRAPH p) (GR bj bk :: GRAPH p)
instance (ThinProfunctor p) => Profunctor (Graph :: CAT (GRAPH p)) where
  dimap = dimapDefault
  r \\ Graph f g = r \\ f \\ g
instance (ThinProfunctor p) => Promonad (Graph :: CAT (GRAPH p)) where
  id = Graph id id
  Graph f1 g1 . Graph f2 g2 = Graph (f1 . f2) (g1 . g2)

-- | The graph of a thin profunctor. Doing this for any profunctor would need dependent types.
instance (ThinProfunctor p) => CategoryOf (GRAPH p) where
  type (~>) = Graph
  type
    Ob @(GRAPH p) ab =
      (ab ~ GR (ProjJ p @ ab) (ProjK p @ ab), Ob (ProjJ p @ ab), Ob (ProjK p @ ab), HasArrow p (ProjJ p @ ab) (ProjK p @ ab))

-- | A morphism gives two equal ways to compute the "diagonal", which is an element of the profunctor.
diagonalElement
  :: forall {j} {k} (p :: k +-> j) (aj :: j) (ak :: k) (bj :: j) (bk :: k) r
   . (ThinProfunctor p) => GR aj ak ~> (GR bj bk :: GRAPH p) -> ((HasArrow p aj bk, Ob aj, Ob bk) => r) -> r
diagonalElement (Graph f g) = withArr @p @aj @bk (lmap f (arr @p @bj @bk) \\ f \\ g)

graphUniv :: forall {j} {k} (p :: k +-> j). (ThinProfunctor p) => Iso' p (Rep (ProjJ p) :.: Corep (ProjK p))
graphUniv =
  iso
    (Prof \ @a @b p -> withArr p (Rep @_ @_ @(GR a b) id :.: Corep id))
    (Prof \(Rep l :.: Corep r) -> dimap l r arr)

data family ProdAsGraph :: (j, k) +-> GRAPH (p :: k +-> j)
instance (CategoryOf j, CategoryOf k, CodiscreteProfunctor p) => FunctorForRep (ProdAsGraph :: (j, k) +-> GRAPH (p :: k +-> j)) where
  type ProdAsGraph @ '(a, b) = GR a b
  fmap (l :**: r) = Graph l r \\ l \\ r

-- | The arrow category is the graph of the hom-functor. Here we require the category to be thin.
type ARROW k = GRAPH (Id :: CAT k)

-- | The category of elements of a functor.
type ELEMENTS f = GRAPH (Rep f)

-- | The comma category f/g is the graph of @C(f(-), g(=))@.
type f `COMMA` g = GRAPH (Direp f g)