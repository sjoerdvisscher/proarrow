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


type Comp :: TENSOR (PRO k k)
data Comp p qr where
  Comp :: (Profunctor q, Profunctor r) => p ~> q :.: r -> Comp p '(q, r)

instance CategoryOf k => Profunctor (Comp :: TENSOR (PRO k k)) where
  dimap l r@(:**:){} (Comp f) = Comp (repMap @Comp r . f . l) \\ r
  r \\ Comp f = r \\ f

instance CategoryOf k => Representable (Comp :: TENSOR (PRO k k)) where
  type Comp % '(p, q) = p :.: q
  index (Comp f) = f
  tabulate = Comp
  repMap (f :**: g) = getNat (map f) . map g \\ f \\ g

instance CategoryOf k => Tensor (Comp :: TENSOR (PRO k k)) where
  type U Comp = Id
  leftUnitor = Prof \(Id f :.: p) -> lmap f p
  leftUnitorInv = Prof \p -> Id id :.: p \\ p
  rightUnitor = Prof \(p :.: Id f) -> rmap f p
  rightUnitorInv = Prof \p -> p :.: Id id \\ p
  associator' Prof{} Prof{} Prof{} = Prof \((p :.: q) :.: r) -> p :.: (q :.: r)
  associatorInv' Prof{} Prof{} Prof{} = Prof \(p :.: (q :.: r)) -> (p :.: q) :.: r