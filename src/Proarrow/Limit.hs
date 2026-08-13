{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Limit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Category.Instance.Coproduct (COPRODUCT, IsLR (..), L, R)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), rmap, (//), (:~>), type (+->))
import Proarrow.Functor (Functor (..), FunctorForRep (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), fst, snd)
import Proarrow.Limit.Power (Powered (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..), terminate)
import Proarrow.Profunctor.Corepresentable (Corep (..), corepUniv)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.HaskValue (HaskValue (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), repUniv, withObRep)

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

instance (HasTerminalObject k) => HasLimits (Unweighted :: VOID +-> ()) k where
  type Limit Unweighted d = Rep (Constant TerminalObject)
  limit (_ :.: t) = case t of {}
  limitUniv _ p = p // Rep terminate

type O1 = L '()
type O2 = R '()
type At1 d = d % O1
type At2 d = d % O2

data family ProductLimit :: COPRODUCT () () +-> k -> () +-> k
instance (HasBinaryProducts k, Representable d) => FunctorForRep (ProductLimit d :: () +-> k) where
  type ProductLimit d @ '() = At1 d && At2 d
  fmap Unit = withObRep @d @O1 $ withObRep @d @O2 $ withObProd @_ @(At1 d) @(At2 d) id

instance (HasBinaryProducts k) => HasLimits (Unweighted :: COPRODUCT () () +-> ()) k where
  type Limit Unweighted d = Rep (ProductLimit d)
  limit @d (Rep f :.: TerminalProfunctor @_ @o) =
    withObRep @d @O1 $
      withObRep @d @O2 $
        lrCase @o
          (tabulate (fst @_ @(At1 d) @(At2 d) . f))
          (tabulate (snd @_ @(At1 d) @(At2 d) . f))
  limitUniv n p = p // Rep (index (n (p :.: TerminalProfunctor @'() @O1)) &&& index (n (p :.: TerminalProfunctor @'() @O2)))

data family PowerLimit :: v -> () +-> k -> () +-> k
instance (Representable d, Powered v k, Ob n) => FunctorForRep (PowerLimit (n :: v) d :: () +-> k) where
  type PowerLimit n d @ '() = (d % '()) ^ n
  fmap Unit = withObRep @d @'() $ withObPower @v @k @(d % '()) @n id
instance (Powered Type k) => HasLimits (HaskValue n :: () +-> ()) k where
  type Limit (HaskValue n) d = Rep (PowerLimit n d)
  limit @d (Rep f :.: HaskValue n) = withObRep @d @'() $ tabulate (unpower f n)
  limitUniv @d m p = withObRep @d @'() $ Rep (power \n -> index (m (p :.: HaskValue n))) \\ p

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

instance (FunctorForRep f) => HasLimits (Corep f) k where
  type Limit (Corep f) d = d :.: Rep f
  limit ((d :.: Rep f) :.: Corep g) = rmap (g . f) d
  limitUniv n p = p // n (p :.: corepUniv) :.: repUniv

newtype AnyLimit j a b = AnyLimit (j a b)
  deriving newtype (Profunctor)
type Ran :: (i +-> a) -> (i +-> Type) -> a -> Type
newtype Ran j d a = Ran {runRan :: forall b. j a b -> d % b}
instance (Profunctor j, Representable d) => Functor (Ran j d) where
  map f (Ran g) = Ran \j -> g (lmap f j)
instance (Profunctor j) => HasLimits (AnyLimit j) Type where
  type Limit (AnyLimit j) d = Star (Ran j d)
  limit (Star f :.: AnyLimit j) = tabulate (\a -> runRan (f a) j) \\ j
  limitUniv n p = p // Star (\a -> Ran \j -> index (n (p :.: AnyLimit j)) a)