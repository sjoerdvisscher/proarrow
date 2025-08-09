{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Limit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT, L, R, pattern InjL, pattern InjR)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), lmap, rmap, (//), (:~>), type (+->))
import Proarrow.Object (Obj, tgt)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), fst, snd)
import Proarrow.Object.Power (Powered (..))
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.HaskValue (HaskValue (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep, repObj, withRepOb, CorepStar (..))
import Proarrow.Profunctor.Terminal (TerminalProfunctor (TerminalProfunctor'))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep)
import Proarrow.Profunctor.Wrapped (Wrapped)

class (Representable (Limit j d)) => IsRepresentableLimit j d
instance (Representable (Limit j d)) => IsRepresentableLimit j d

-- | profunctor-weighted limits
type HasLimits :: forall {a} {i}. i +-> a -> Kind -> Constraint
class (Profunctor j, forall (d :: i +-> k). (Representable d) => IsRepresentableLimit j d) => HasLimits (j :: i +-> a) k where
  type Limit (j :: i +-> a) (d :: i +-> k) :: a +-> k
  limit :: (Representable (d :: i +-> k)) => Limit j d :.: j :~> d
  limitUniv :: (Representable (d :: i +-> k), Profunctor p) => p :.: j :~> d -> p :~> Limit j d

rightAdjointPreservesLimits
  :: forall {k} {k'} {i} {a} (f :: k' +-> k) (g :: k +-> k') (d :: i +-> k) (j :: i +-> a)
   . (Adjunction f g, Representable d, Representable f, Representable g, HasLimits j k, HasLimits j k')
  => Limit j (g :.: d) :~> g :.: Limit j d
rightAdjointPreservesLimits lim =
  lim // case unit @f @g of
    g :.: f ->
      g
        :.: limitUniv @j @k @d
          (\((f' :.: lim') :.: j) -> case limit @j @k' @(g :.: d) (lim' :.: j) of g' :.: d -> lmap (counit (f' :.: g')) d)
          (f :.: lim)

rightAdjointPreservesLimitsInv
  :: forall {k} {k'} {i} {a} (g :: k +-> k') (d :: i +-> k) (j :: i +-> a)
   . (Representable d, Representable g, HasLimits j k, HasLimits j k')
  => g :.: Limit j d :~> Limit j (g :.: d)
rightAdjointPreservesLimitsInv = limitUniv @j @k' @(g :.: d) (\((g :.: lim) :.: j) -> g :.: limit (lim :.: j))

type Unweighted = TerminalProfunctor

type TerminalLimit :: VOID +-> k -> () +-> k
data TerminalLimit d a b where
  TerminalLimit :: forall d a. a ~> TerminalObject -> TerminalLimit d a '()

instance (HasTerminalObject k) => Profunctor (TerminalLimit (d :: VOID +-> k)) where
  dimap = dimapRep
  r \\ TerminalLimit f = r \\ f
instance (HasTerminalObject k) => Representable (TerminalLimit (d :: VOID +-> k)) where
  type TerminalLimit d % '() = TerminalObject
  index (TerminalLimit f) = f
  tabulate = TerminalLimit
  repMap Unit = id

instance (HasTerminalObject k) => HasLimits (Unweighted :: VOID +-> ()) k where
  type Limit Unweighted d = TerminalLimit d
  limit = \case {}
  limitUniv _ p = p // TerminalLimit terminate

type ProductLimit :: COPRODUCT () () +-> k -> () +-> k
data ProductLimit d a b where
  ProductLimit :: forall d a. a ~> ProductLimit d % '() -> ProductLimit d a '()

instance (HasBinaryProducts k, Representable d) => Profunctor (ProductLimit d :: () +-> k) where
  dimap = dimapRep
  r \\ (ProductLimit f) = r \\ f
instance (HasBinaryProducts k, Representable d) => Representable (ProductLimit d :: () +-> k) where
  type ProductLimit d % '() = (d % L '()) && (d % R '())
  index (ProductLimit f) = f
  tabulate = ProductLimit
  repMap Unit = (***) @_ @(d % L '()) @(d % R '()) (repMap @d (InjL Unit)) (repMap @d (InjR Unit))

instance (HasBinaryProducts k) => HasLimits (Unweighted :: COPRODUCT () () +-> ()) k where
  type Limit Unweighted d = ProductLimit d
  limit (ProductLimit @d f :.: TerminalProfunctor' _ o) = o // tabulate $ choose @_ @d o . f
  limitUniv n p =
    p //
      let l = n (p :.: TerminalProfunctor' Unit (InjL Unit))
          r = n (p :.: TerminalProfunctor' Unit (InjR Unit))
      in ProductLimit $ index l &&& index r

choose
  :: forall k (d :: COPRODUCT () () +-> k) b
   . (HasBinaryProducts k, Representable d)
  => Obj b
  -> ((d % L '()) && (d % R '())) ~> (d % b)
choose b = withRepOb @d @(L '()) $ withRepOb @d @(R '()) $ case b of
  (InjL Unit) -> fst @_ @(d % L '()) @(d % R '())
  (InjR Unit) -> snd @_ @(d % L '()) @(d % R '())

type PowerLimit :: v -> () +-> k -> () +-> k
data PowerLimit n d a b where
  PowerLimit :: forall n d a. (a ~> PowerLimit n d % '()) -> PowerLimit n d a '()
instance (Representable d, Powered v k, Ob n) => Profunctor (PowerLimit (n :: v) d :: () +-> k) where
  dimap = dimapRep
  r \\ PowerLimit f = r \\ f
instance (Representable d, Powered v k, Ob n) => Representable (PowerLimit (n :: v) d :: () +-> k) where
  type PowerLimit n d % '() = (d % '()) ^ n
  index (PowerLimit f) = f
  tabulate = PowerLimit
  repMap Unit = withObPower @v @k @(d % '()) @n id \\ repObj @d @'()
instance (Powered Type k) => HasLimits (HaskValue n :: () +-> ()) k where
  type Limit (HaskValue n) d = PowerLimit n d
  limit @d (PowerLimit f :.: HaskValue n) = tabulate (unpower f n) \\ repObj @d @'()
  limitUniv @d m p = PowerLimit (power \n -> index (m (p :.: HaskValue n))) \\ p \\ repObj @d @'()

newtype End d = End {unEnd :: forall a b. a ~> b -> d % '(OP a, b)}

type EndLimit :: (OPPOSITE k, k) +-> Type -> () +-> Type
data EndLimit d a b where
  EndLimit :: forall d a. (a -> End d) -> EndLimit d a '()

instance (Representable d) => Profunctor (EndLimit (d :: (OPPOSITE k, k) +-> Type)) where
  dimap = dimapRep
  r \\ EndLimit f = r \\ f
instance (Representable d) => Representable (EndLimit (d :: (OPPOSITE k, k) +-> Type)) where
  type EndLimit d % '() = End d
  index (EndLimit f) = f
  tabulate = EndLimit
  repMap Unit = id

type Hom :: (OPPOSITE k, k) +-> ()
data Hom a b where
  Hom :: a ~> b -> Hom '() '(OP a, b)
instance (CategoryOf k) => Profunctor (Hom :: (OPPOSITE k, k) +-> ()) where
  dimap Unit (Op l :**: r) (Hom f) = Hom (r . f . l) \\ l \\ r
  r \\ Hom f = r \\ f

instance (CategoryOf k) => HasLimits (Hom :: (OPPOSITE k, k) +-> ()) Type where
  type Limit Hom d = EndLimit d
  limit (EndLimit f :.: Hom k) = k // tabulate (\a -> unEnd (f a) k)
  limitUniv n p = p // EndLimit \a -> End \x -> index (n (p :.: Hom x)) a

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
