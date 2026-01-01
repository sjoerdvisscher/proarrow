{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Limit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Category.Instance.Coproduct (COPRODUCT, IsLR (..), L, R, pattern InjL, pattern InjR)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), rmap, tgt, (//), (:~>), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), fst, snd)
import Proarrow.Object.Power (Powered (..))
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep)
import Proarrow.Profunctor.HaskValue (HaskValue (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), Representable (..), repObj, withRepOb)
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Wrapped (Wrapped)

class (Representable (Limit j d)) => IsRepresentableLimit j d
instance (Representable (Limit j d)) => IsRepresentableLimit j d

-- | profunctor-weighted limits
type HasLimits :: forall {a} {i}. i +-> a -> Kind -> Constraint
class (Profunctor j, forall (d :: i +-> k). (Representable d) => IsRepresentableLimit j d) => HasLimits (j :: i +-> a) k where
  type Limit (j :: i +-> a) (d :: i +-> k) :: a +-> k
  limit :: (Representable (d :: i +-> k)) => Limit j d :.: j :~> d
  limitUniv :: (Representable (d :: i +-> k), Profunctor p) => p :.: j :~> d -> p :~> Limit j d

mapLimit
  :: forall {i} j k p q. (HasLimits j k, Representable p, Representable q) => (p :: i +-> k) ~> q -> Limit j p ~> Limit j q
mapLimit (Prof n) = Prof (limitUniv @j (n . limit @j))

type Unweighted = TerminalProfunctor

data family TerminalLimit :: VOID +-> k -> () +-> k
instance (HasTerminalObject k) => FunctorForRep (TerminalLimit d :: () +-> k) where
  type TerminalLimit d @ a = TerminalObject
  fmap Unit = id

instance (HasTerminalObject k) => HasLimits (Unweighted :: VOID +-> ()) k where
  type Limit Unweighted d = Rep (TerminalLimit d)
  limit = \case {}
  limitUniv _ p = p // Rep terminate

data family ProductLimit :: COPRODUCT () () +-> k -> () +-> k
instance (HasBinaryProducts k, Representable d) => FunctorForRep (ProductLimit d :: () +-> k) where
  type ProductLimit d @ '() = (d % L '()) && (d % R '())
  fmap Unit = (***) @_ @(d % L '()) @(d % R '()) (repMap @d (InjL Unit)) (repMap @d (InjR Unit))

instance (HasBinaryProducts k) => HasLimits (Unweighted :: COPRODUCT () () +-> ()) k where
  type Limit Unweighted d = Rep (ProductLimit d)
  limit (Rep @(ProductLimit d) f :.: TerminalProfunctor @_ @o) = tabulate $ choose @d @o . f
  limitUniv n p =
    p //
      let l = n (p :.: TerminalProfunctor' Unit (InjL Unit))
          r = n (p :.: TerminalProfunctor' Unit (InjR Unit))
      in Rep $ index l &&& index r

choose
  :: forall {k} (d :: COPRODUCT () () +-> k) b
   . (HasBinaryProducts k, Representable d, Ob b)
  => ((d % L '()) && (d % R '())) ~> (d % b)
choose =
  withRepOb @d @(L '()) $
    withRepOb @d @(R '()) $
      caseLr @b
        (fst @_ @(d % L '()) @(d % R '()))
        (snd @_ @(d % L '()) @(d % R '()))

data family PowerLimit :: v -> () +-> k -> () +-> k
instance (Representable d, Powered v k, Ob n) => FunctorForRep (PowerLimit (n :: v) d :: () +-> k) where
  type PowerLimit n d @ '() = (d % '()) ^ n
  fmap Unit = withObPower @v @k @(d % '()) @n id \\ repObj @d @'()
instance (Powered Type k) => HasLimits (HaskValue n :: () +-> ()) k where
  type Limit (HaskValue n) d = Rep (PowerLimit n d)
  limit @d (Rep f :.: HaskValue n) = tabulate (unpower f n) \\ repObj @d @'()
  limitUniv @d m p = Rep (power \n -> index (m (p :.: HaskValue n))) \\ p \\ repObj @d @'()

newtype End d = End {unEnd :: forall a b. a ~> b -> d % '(OP a, b)}

data family EndLimit :: (OPPOSITE k, k) +-> Type -> () +-> Type
instance (Representable d) => FunctorForRep (EndLimit (d :: (OPPOSITE k, k) +-> Type)) where
  type EndLimit d @ '() = End d
  fmap Unit = id

type Hom :: (OPPOSITE k, k) +-> ()
data Hom a b where
  Hom :: a ~> b -> Hom '() '(OP a, b)
instance (CategoryOf k) => Profunctor (Hom :: (OPPOSITE k, k) +-> ()) where
  dimap Unit (Op l :**: r) (Hom f) = Hom (r . f . l) \\ l \\ r
  r \\ Hom f = r \\ f

instance (CategoryOf k) => HasLimits (Hom :: (OPPOSITE k, k) +-> ()) Type where
  type Limit Hom d = Rep (EndLimit d)
  limit (Rep f :.: Hom k) = k // tabulate (\a -> unEnd (f a) k)
  limitUniv n p = p // Rep \a -> End \x -> index (n (p :.: Hom x)) a

instance (CategoryOf j) => HasLimits (Id :: CAT j) k where
  type Limit Id d = d
  limit (d :.: Id f) = rmap f d
  limitUniv n p = n (p :.: Id id) \\ p

instance (Representable j1, HasLimits j1 k, HasLimits j2 k) => HasLimits (j1 :.: j2) k where
  type Limit (j1 :.: j2) d = Limit j1 (Limit j2 d)
  limit @d (l :.: (j1 :.: j2)) = limit @j2 @k @d (limit @j1 @k @(Limit j2 d) (l :.: j1) :.: j2)
  limitUniv @d n = limitUniv @j1 @k @(Limit j2 d) (limitUniv @j2 @k @d (\((p' :.: j1) :.: j2) -> n (p' :.: (j1 :.: j2))))

instance (Corepresentable j) => HasLimits (Wrapped j) k where
  type Limit (Wrapped j) d = d :.: CorepStar j
  limit ((d :.: CorepStar f) :.: g) = rmap (coindex g . f) d
  limitUniv n p = p // n (p :.: trivialCorep) :.: CorepStar (corepMap @j (tgt p))
