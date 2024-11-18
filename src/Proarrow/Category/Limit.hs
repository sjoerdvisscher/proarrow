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
import Proarrow.Core (CategoryOf (..), Kind, Profunctor (..), Promonad (..), lmap, (//), (:~>), type (+->))
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), fst, snd)
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep, withRepObj)
import Proarrow.Profunctor.Terminal (TerminalProfunctor (TerminalProfunctor'))

class (Representable (Limit j d)) => IsRepresentableLimit j d
instance (Representable (Limit j d)) => IsRepresentableLimit j d

-- | profunctor-weighted limits
type HasLimits :: forall {a} {i}. i +-> a -> Kind -> Constraint
class (Profunctor j, forall (d :: i +-> k). (Representable d) => IsRepresentableLimit j d) => HasLimits (j :: i +-> a) k where
  type Limit (j :: i +-> a) (d :: i +-> k) :: a +-> k
  limit :: (Representable (d :: i +-> k)) => Limit j d :.: j :~> d
  limitUniv :: (Representable (d :: i +-> k), Representable p) => p :.: j :~> d -> p :~> Limit j d

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
  limit = \case
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
    p
      // let l = n (p :.: TerminalProfunctor' Unit (InjL Unit))
             r = n (p :.: TerminalProfunctor' Unit (InjR Unit))
         in ProductLimit $ index l &&& index r

choose
  :: forall k (d :: COPRODUCT () () +-> k) b
   . (HasBinaryProducts k, Representable d)
  => Obj b
  -> ((d % L '()) && (d % R '())) ~> (d % b)
choose b = withRepObj @d @(L '()) $ withRepObj @d @(R '()) $ case b of
  (InjL Unit) -> fst @_ @(d % L '()) @(d % R '())
  (InjR Unit) -> snd @_ @(d % L '()) @(d % R '())

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