{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Representable where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Enriched.ThinCategory (Discrete, Thin, ThinProfunctor (..), withEq)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (:~>), type (+->), rmap, Iso, iso)
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object (Obj, obj, tgt, src)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep, trivialCorep)
import Proarrow.Category.Instance.Prof (Prof(..))

infixl 8 %

type Representable :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => Representable (p :: j +-> k) where
  type p % (a :: j) :: k
  index :: p a b -> a ~> p % b
  tabulate :: (Ob b) => (a ~> p % b) -> p a b
  repMap :: (a ~> b) -> p % a ~> p % b
  repMap f = index @p (rmap f trivialRep) \\ f

instance Representable (->) where
  type (->) % a = a
  index f = f
  tabulate f = f

repObj :: forall p a. (Representable p, Ob a) => Obj (p % a)
repObj = repMap @p (obj @a)

withRepOb :: forall p a r. (Representable p, Ob a) => ((Ob (p % a)) => r) -> r
withRepOb r = r \\ repObj @p @a

dimapRep :: forall p a b c d. (Representable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapRep l r = tabulate @p . dimap l (repMap @p r) . index \\ r

trivialRep :: forall p a. (Representable p, Ob a) => p (p % a) a
trivialRep = tabulate (repObj @p @a)

type CorepStar :: (k +-> j) -> (j +-> k)
data CorepStar p a b where
  CorepStar :: (Ob b) => {unCorepStar :: a ~> p %% b} -> CorepStar p a b
instance (Corepresentable p) => Profunctor (CorepStar p) where
  dimap = dimapRep
  r \\ CorepStar f = r \\ f
instance (Corepresentable p) => Representable (CorepStar p) where
  type CorepStar p % a = p %% a
  index (CorepStar f) = f
  tabulate = CorepStar
  repMap = corepMap @p

mapCorepStar :: (Corepresentable p, Corepresentable q) => p ~> q -> CorepStar q ~> CorepStar p
mapCorepStar (Prof n) = Prof \(CorepStar @a f) -> CorepStar (coindex (n (trivialCorep @_ @a)) . f)

type RepCostar :: (k +-> j) -> (j +-> k)
data RepCostar p a b where
  RepCostar :: (Ob a) => {unRepCostar :: p % a ~> b} -> RepCostar p a b
instance (Representable p) => Profunctor (RepCostar p) where
  dimap = dimapCorep
  r \\ RepCostar f = r \\ f
instance (Representable p) => Corepresentable (RepCostar p) where
  type RepCostar p %% a = p % a
  coindex (RepCostar f) = f
  cotabulate = RepCostar
  corepMap = repMap @p
instance (Representable p, Discrete j, Thin k) => ThinProfunctor (RepCostar p :: j +-> k) where
  type HasArrow (RepCostar p) a b = (p % a) ~ b
  arr = RepCostar id
  withArr (RepCostar f) r = withEq f r

mapRepCostar :: (Representable p, Representable q) => p ~> q -> RepCostar q ~> RepCostar p
mapRepCostar (Prof n) = Prof \(RepCostar @a f) -> RepCostar (f . index (n (trivialRep @_ @a)))

flipRep :: forall p. (Representable p) => (~>) :~> p -> RepCostar p :~> (~>)
flipRep n p = coindex p . index (n (src p))

unflipRep :: forall p. (Representable p) => RepCostar p :~> (~>) -> (~>) :~> p
unflipRep n f = tabulate (n (RepCostar (repMap @p f))) \\ f

flipCorep :: forall p. (Corepresentable p) => (~>) :~> p -> CorepStar p :~> (~>)
flipCorep n p = coindex (n (tgt p)) . index p

unflipCorep :: forall p. (Corepresentable p) => CorepStar p :~> (~>) -> (~>) :~> p
unflipCorep n f = cotabulate (n (CorepStar (corepMap @p f))) \\ f

type Rep :: (j +-> k) -> j +-> k
data Rep f a b where
  Rep :: forall f a b. (Ob b) => {unRep :: a ~> f @ b} -> Rep f a b
instance (FunctorForRep f) => Profunctor (Rep f) where
  dimap = dimapRep
  r \\ Rep f = r \\ f
instance (FunctorForRep f) => Representable (Rep f) where
  type Rep f % a = f @ a
  index (Rep f) = f
  tabulate = Rep
  repMap = fmap @f

rep :: forall f a b a' b'. Ob b => Iso (a ~> f @ b) (a' ~> f @ b') (Rep f a b) (Rep f a' b')
rep = iso Rep unRep