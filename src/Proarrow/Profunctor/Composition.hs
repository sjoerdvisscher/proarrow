module Proarrow.Profunctor.Composition where

import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, type (+->), tgt)
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), withCorepObj)
import Proarrow.Profunctor.Representable (Representable (..), withRepObj)
import Proarrow.Category.Monoidal.Action (Strong (..))

type (:.:) :: (j +-> k) -> (i +-> j) -> (i +-> k)
data (p :.: q) a c where
  (:.:) :: p a b -> q b c -> (p :.: q) a c

instance (Profunctor p, Profunctor q) => Profunctor (p :.: q) where
  dimap l r (p :.: q) = lmap l p :.: rmap r q
  r \\ p :.: q = r \\ p \\ q

instance (Profunctor p) => Functor ((:.:) p) where
  map (Prof n) = Prof \(p :.: q) -> p :.: n q

instance Functor (:.:) where
  map (Prof n) = Nat (Prof \(p :.: q) -> n p :.: q)

bimapComp :: (a ~> b) -> (c ~> d) -> a :.: c ~> b :.: d
bimapComp f g = unNat (map f) . map g \\ f \\ g

instance (Representable p, Representable q) => Representable (p :.: q) where
  type (p :.: q) % a = p % (q % a)
  index (p :.: q) = repMap @p (index q) . index p
  tabulate :: forall a b. (Ob b) => (a ~> ((p :.: q) % b)) -> (:.:) p q a b
  tabulate f = withRepObj @q @b (tabulate f :.: tabulate id)
  repMap f = repMap @p (repMap @q f)

instance (Corepresentable p, Corepresentable q) => Corepresentable (p :.: q) where
  type (p :.: q) %% a = q %% (p %% a)
  coindex (p :.: q) = coindex q . corepMap @q (coindex p)
  cotabulate :: forall a b. (Ob a) => (((p :.: q) %% a) ~> b) -> (:.:) p q a b
  cotabulate f = withCorepObj @p @a (cotabulate id :.: cotabulate f)
  corepMap f = corepMap @q (corepMap @p f)

instance (MonoidalProfunctor p, MonoidalProfunctor q) => MonoidalProfunctor (p :.: q) where
  par0 = par0 :.: par0
  (p :.: q) `par` (r :.: s) = (p `par` r) :.: (q `par` s)

instance (Strong m p, Strong m q) => Strong m (p :.: q) where
  act f (p :.: q) = act f p :.: act (tgt f) q

-- | Horizontal composition
o
  :: forall {i} {j} {k} (p :: j +-> k) (q :: j +-> k) (r :: i +-> j) (s :: i +-> j)
   . Prof p q
  -> Prof r s
  -> Prof (p :.: r) (q :.: s)
Prof pq `o` Prof rs = Prof \(p :.: r) -> pq p :.: rs r
