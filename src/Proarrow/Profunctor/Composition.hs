module Proarrow.Profunctor.Composition where

import Proarrow.Core (PRO, Profunctor(..), CategoryOf(..), Promonad (..), lmap, rmap)
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Nat (Nat(..))
import Proarrow.Profunctor.Representable (Representable(..), withRepCod)
import Proarrow.Profunctor.Corepresentable (Corepresentable(..), withCorepCod)


type (:.:) :: PRO i j -> PRO j k -> PRO i k
data (p :.: q) a c where
  (:.:) :: p a b -> q b c -> (p :.: q) a c

instance (Profunctor p, Profunctor q) => Profunctor (p :.: q) where
  dimap l r (p :.: q) = lmap l p :.: rmap r q
  r \\ p :.: q = r \\ p \\ q

instance Profunctor p => Functor ((:.:) p) where
  map (Prof n) = Prof \(p :.: q) -> p :.: n q

instance Functor (:.:) where
  map (Prof n) = Nat (Prof \(p :.: q) -> n p :.: q)

bimapComp :: (a ~> b) -> (c ~> d) -> a :.: c ~> b :.: d
bimapComp f g = getNat (map f) . map g \\ f \\ g

instance (Representable p, Representable q) => Representable (p :.: q) where
  type (p :.: q) % a = p % (q % a)
  index (p :.: q) = repMap @p (index q) . index p
  tabulate :: forall a b. Ob b => (a ~> ((p :.: q) % b)) -> (:.:) p q a b
  tabulate f = withRepCod @q @b (tabulate f :.: tabulate id)
  repMap f = repMap @p (repMap @q f)

instance (Corepresentable p, Corepresentable q) => Corepresentable (p :.: q) where
  type (p :.: q) %% a = q %% (p %% a)
  coindex (p :.: q) = coindex q . corepMap @q (coindex p)
  cotabulate :: forall a b. Ob a => (((p :.: q) %% a) ~> b) -> (:.:) p q a b
  cotabulate f = withCorepCod @p @a (cotabulate id :.: cotabulate f)
  corepMap f = corepMap @q (corepMap @p f)


-- | Horizontal composition
o :: forall {i} {j} {k} (p :: PRO i j) (q :: PRO i j) (r :: PRO j k) (s :: PRO j k)
  . Prof p q -> Prof r s -> Prof (p :.: r) (q :.: s)
Prof pq `o` Prof rs = Prof \(p :.: r) -> pq p :.: rs r
