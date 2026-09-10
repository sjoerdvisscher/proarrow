-- | A third way to combine two flavors, alongside "Proarrow.Optic.Sum" and "Proarrow.Optic.Day":
-- pair them up over the /product/ of two categories via ':**:'.
module Proarrow.Optic.Prod where

import Proarrow.Category.Instance.Product (Fst, Snd, (:**:) (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), (\\), type (+->))
import Proarrow.Functor (type (@))
import Proarrow.Optic (FLAVOR, Flavor, Optic, Prostrong (..), legs2prof, withLegs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

-- | Two flavors combine into one over the product of their (possibly heterogeneous) categories,
-- by pairing up their witness profunctors componentwise via ':**:' rather than sharing a single
-- object (@:*:@ doesn't work here: it forces both witnesses onto the *same* index kind, so it
-- can't combine optics over genuinely different categories/objects).
type ProdRes :: forall {j1} {k1} {j2} {k2}. FLAVOR j1 k1 -> FLAVOR j2 k2 -> FLAVOR (j1, j2) (k1, k2)
class ProdRes w1 w2 (p :: (k1, k2) +-> (k1, k2)) (q :: (j1, j2) +-> (j1, j2)) where
  -- | Recover the two component witnesses from an opaque, possibly-composite 'ProdRes' pair.
  -- Stated via 'Fst'\/'Snd' rather than literal tuple patterns: the existential "middle" object
  -- introduced when recursing through a ':.:' composite isn't syntactically a tuple, even though
  -- (being of a product kind) it always denotes one.
  withProdP
    :: p s a
    -> q b t
    -> ( forall p1 p2 q1 q2
          . (w1 p1 q1, w2 p2 q2, Profunctor p1, Profunctor p2, Profunctor q1, Profunctor q2)
         => p1 (Fst @ s) (Fst @ a) -> p2 (Snd @ s) (Snd @ a) -> q1 (Fst @ b) (Fst @ t) -> q2 (Snd @ b) (Snd @ t) -> r
       )
    -> r

instance
  (w1 p1 q1, w2 p2 q2, Profunctor p1, Profunctor p2, Profunctor q1, Profunctor q2)
  => ProdRes w1 w2 (p1 :**: p2) (q1 :**: q2)
  where
  withProdP (l1 :**: l2) (r1 :**: r2) k = k l1 l2 r1 r2
instance
  (CategoryOf k1, CategoryOf k2, CategoryOf j1, CategoryOf j2, Flavor w1, Flavor w2)
  => ProdRes w1 w2 (Id :: CAT (k1, k2)) (Id :: CAT (j1, j2))
  where
  withProdP (Id (f1 :**: f2)) (Id (g1 :**: g2)) k = k (Id f1) (Id f2) (Id g1) (Id g2)
instance
  (ProdRes w1 w2 f f', ProdRes w1 w2 g g', Flavor w1, Flavor w2)
  => ProdRes w1 w2 (f :.: g) (g' :.: f')
  where
  withProdP (f :.: g) (g' :.: f') k =
    withProdP @w1 @w2 f f' \p1 p2 q1 q2 ->
      withProdP @w1 @w2 g g' \p1' p2' q1' q2' ->
        k (p1 :.: p1') (p2 :.: p2') (q1' :.: q1) (q2' :.: q2)

prodOptic
  :: forall {j1} {k1} {j2} {k2} (w1 :: FLAVOR j1 k1) (w2 :: FLAVOR j2 k2) s1 t1 a1 b1 s2 t2 a2 b2
   . (Flavor w1, Flavor w2, CategoryOf j1, CategoryOf k1, CategoryOf j2, CategoryOf k2)
  => Optic (Prostrong w1) s1 t1 a1 b1
  -> Optic (Prostrong w2) s2 t2 a2 b2
  -> Optic (Prostrong (ProdRes w1 w2)) '(s1, s2) '(t1, t2) '(a1, a2) '(b1, b2)
prodOptic o1 o2 =
  withLegs @w1 o1 \l1 r1 ->
    withLegs @w2 o2 \l2 r2 ->
      legs2prof @(ProdRes w1 w2) (l1 :**: l2) (r1 :**: r2) \\ l1 \\ r1 \\ l2 \\ r2

-- | The inverse of 'prodOptic': split a @'ProdRes' w1 w2@-flavored optic back into its two
-- independent halves.
withProdOptic
  :: forall {j1} {k1} {j2} {k2} (w1 :: FLAVOR j1 k1) (w2 :: FLAVOR j2 k2) s1 t1 a1 b1 s2 t2 a2 b2 r
   . (CategoryOf j1, CategoryOf k1, CategoryOf j2, CategoryOf k2, Flavor w1, Flavor w2)
  => Optic (Prostrong (ProdRes w1 w2)) '(s1, s2) '(t1, t2) '(a1, a2) '(b1, b2)
  -> ((Optic (Prostrong w1) s1 t1 a1 b1, Optic (Prostrong w2) s2 t2 a2 b2) -> r)
  -> r
withProdOptic o k0 =
  withLegs @(ProdRes w1 w2) o \l r ->
    withProdP @w1 @w2 l r \p1 p2 q1 q2 ->
      k0
        (legs2prof @w1 p1 q1, legs2prof @w2 p2 q2)
