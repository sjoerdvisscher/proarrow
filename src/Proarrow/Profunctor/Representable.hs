{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Representable where

import Data.Kind (Constraint)

import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit ()
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), (:~>), type (+->), rmap, lmap)
import Proarrow.Functor (FunctorForRep (..), Presheaf, withMappedOb)
import Proarrow.Object (Obj, obj, src, tgt)
import Proarrow.Optic (Iso, iso)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep, trivialCorep)

infixl 8 %

type Representable :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => Representable (p :: j +-> k) where
  type p % (a :: j) :: k
  index :: p a b -> a ~> p % b
  tabulate :: (Ob b) => (a ~> p % b) -> p a b
  tabulate f = lmap f trivialRep
  repMap :: (a ~> b) -> p % a ~> p % b
  repMap @a f = index @p (rmap f (trivialRep @p @a)) \\ f
  trivialRep :: (Ob a) => p (p % a) a
  trivialRep @a = tabulate (repObj @p @a)
  {-# MINIMAL index, ((tabulate, repMap) | trivialRep) #-}

instance Representable (->) where
  type (->) % a = a
  index f = f
  tabulate f = f
  repMap f = f
  trivialRep = id

instance (Representable p, Representable q) => Representable (p :**: q) where
  type (p :**: q) % '(a, b) = '(p % a, q % b)
  index (p :**: q) = index p :**: index q
  tabulate (f :**: g) = tabulate f :**: tabulate g
  repMap (f :**: g) = repMap @p f :**: repMap @q g
  trivialRep = trivialRep :**: trivialRep

repObj :: forall p a. (Representable p, Ob a) => Obj (p % a)
repObj = repMap @p (obj @a)

withObRep :: forall p a r. (Representable p, Ob a) => ((Ob (p % a)) => r) -> r
withObRep r = r \\ repObj @p @a

dimapRep :: forall p a b c d. (Representable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapRep l r = tabulate @p . dimap l (repMap @p r) . index \\ r

tabulated :: forall p a a' b b'. (Representable p, Ob b) => Iso (a ~> p % b) (a' ~> p % b') (p a b) (p a' b')
tabulated = iso tabulate index

type RepresentablePresheaf (f :: Presheaf k) = Representable f
type Key (f :: Presheaf k) = f % '()
tabulatedPresheaf :: (RepresentablePresheaf f, Ob a) => Iso (a ~> Key f) (a' ~> Key f) (f a '()) (f a' '())
tabulatedPresheaf = tabulated

instance (Representable p) => Corepresentable (Op p) where
  type Op p %% OP a = OP (p % a)
  coindex (Op f) = Op (index f)
  cotabulate (Op f) = Op (tabulate f)
  corepMap (Op f) = Op (repMap @p f)
  trivialCorep = Op trivialRep

instance (Corepresentable p) => Representable (Op p) where
  type Op p % OP a = OP (p %% a)
  index (Op f) = Op (coindex f)
  tabulate (Op f) = Op (cotabulate f)
  repMap (Op f) = Op (corepMap @p f)
  trivialRep = Op trivialCorep

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
instance (Representable p, Thin j) => ThinProfunctor (RepCostar p :: j +-> k) where
  type HasArrow (RepCostar p :: j +-> k) a b = HasArrow (Hom j) (p % a) b
  arr @a = withObRep @p @a (RepCostar arr)
  withArr (RepCostar f) r = withArr f r

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
instance (FunctorForRep f, Thin k) => ThinProfunctor (Rep f :: j +-> k) where
  type HasArrow (Rep f :: j +-> k) a b = HasArrow (Hom k) a (f @ b)
  arr @_ @b = withMappedOb @f @b (Rep arr)
  withArr (Rep f) r = withArr f r

rep :: forall f a b a' b'. (FunctorForRep f, Ob b) => Iso (a ~> f @ b) (a' ~> f @ b') (Rep f a b) (Rep f a' b')
rep = tabulated

type Monad m = (Promonad m, Representable m)

return :: forall m a. (Monad m, Ob a) => a ~> m % a
return = index @m id

bind :: forall m a b. (Monad m, Ob b) => (a ~> m % b) -> (m % a ~> m % b)
bind f = index (tabulate @m @b f . (trivialRep \\ f))
