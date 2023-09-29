module Proarrow.Profunctor.Composition where

import Proarrow.Core (PRO, Profunctor(..), Category(..), type (~>), lmap, rmap, CategoryOf)
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Nat (Nat(..))
import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (Tensor(..), TENSOR)
import Proarrow.Profunctor.Identity (Id (..))
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

instance (Representable p, Representable q) => Representable (p :.: q) where
  type (p :.: q) % a = p % (q % a)
  index (p :.: q) = repMap @q (index p) . index q
  tabulate :: forall a b. Ob b => (a ~> ((p :.: q) % b)) -> (:.:) p q a b
  tabulate f = withRepCod @q @b (tabulate f :.: tabulate id)
  repMap f = repMap @p (repMap @q f)

instance (Corepresentable p, Corepresentable q) => Corepresentable (p :.: q) where
  type (p :.: q) %% a = q %% (p %% a)
  coindex (p :.: q) = corepMap @p (coindex q) . coindex p
  cotabulate :: forall a b. Ob a => (((p :.: q) %% a) ~> b) -> (:.:) p q a b
  cotabulate f = withCorepCod @p @a (cotabulate id :.: cotabulate f)
  corepMap f = corepMap @p (corepMap @q f)


type Compose :: TENSOR (PRO k k)
data Compose p qr where
  Compose :: (Profunctor q, Profunctor r) => p ~> q :.: r -> Compose p '(q, r)

instance CategoryOf k => Profunctor (Compose :: TENSOR (PRO k k)) where
  dimap l r@(:**:){} (Compose f) = Compose (repMap @Compose r . f . l) \\ r
  r \\ Compose f = r \\ f

instance CategoryOf k => Representable (Compose :: TENSOR (PRO k k)) where
  type Compose % '(p, q) = p :.: q
  index (Compose f) = f
  tabulate = Compose
  repMap (f :**: g) = getNat (map f) . map g \\ f \\ g

instance CategoryOf k => Tensor (Compose :: TENSOR (PRO k k)) where
  type U Compose = Id
  leftUnitor = Prof \(Id f :.: p) -> lmap f p
  leftUnitorInv = Prof \p -> Id id :.: p \\ p
  rightUnitor = Prof \(p :.: Id f) -> rmap f p
  rightUnitorInv = Prof \p -> p :.: Id id \\ p
  associator' Prof{} Prof{} Prof{} = Prof \((p :.: q) :.: r) -> p :.: (q :.: r)
  associatorInv' Prof{} Prof{} Prof{} = Prof \(p :.: (q :.: r)) -> (p :.: q) :.: r


-- | Horizontal composition
o :: forall {i} {j} {k} (p :: PRO i j) (q :: PRO i j) (r :: PRO j k) (s :: PRO j k)
  . Prof p q -> Prof r s -> Prof (p :.: r) (q :.: s)
Prof pq `o` Prof rs = Prof \(p :.: r) -> pq p :.: rs r
