{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Limit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), (:++:) (..))
import Proarrow.Category.Instance.Product (Fst, Snd, (:**:) (..))
import Proarrow.Category.Instance.Unit (UNIT (..), Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Kind, PRO, Profunctor (..), Promonad (..), UN, lmap, (//), (:~>))
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), fst, snd)
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep, withRepCod)
import Proarrow.Profunctor.Rift (Rift (..), type (<|))
import Proarrow.Profunctor.Terminal (TerminalProfunctor (TerminalProfunctor'))

class (Representable (Limit j d)) => IsRepresentableLimit j d
instance (Representable (Limit j d)) => IsRepresentableLimit j d

-- | profunctor-weighted limits
type HasLimits :: forall {a} {i}. PRO a i -> Kind -> Constraint
class (forall (d :: PRO k i). (Representable d) => IsRepresentableLimit j d) => HasLimits (j :: PRO a i) k where
  type Limit (j :: PRO a i) (d :: PRO k i) :: PRO k a
  limit :: (Representable (d :: PRO k i)) => Limit j d :~> d <| j
  limitInv :: (Representable (d :: PRO k i)) => d <| j :~> Limit j d

rightAdjointPreservesLimits
  :: forall {k} {i} {a} f g (d :: PRO k i) (j :: PRO a i)
   . (Adjunction f g, Representable d, HasLimits j k)
  => (g :.: d) <| j :~> g :.: Limit j d
rightAdjointPreservesLimits (Rift k) =
  case unit @f @g of
    g :.: f ->
      g :.: limitInv @j @k @d (f // Rift \j -> case k j of g' :.: d -> lmap (counit (f :.: g')) d)

rightAdjointPreservesLimitsInv
  :: forall {k} {i} {a} f g (d :: PRO k i) (j :: PRO a i)
   . (Adjunction f g, Representable d, HasLimits j k)
  => g :.: Limit j (d :: PRO k i) :~> (g :.: d) <| j
rightAdjointPreservesLimitsInv (g :.: l) =
  g // l // Rift \j ->
    case unit @f @g of
      g' :.: f -> g' :.: lmap (counit (f :.: g)) (case limit @j @k @d l of Rift k -> k j)

type Unweighted = TerminalProfunctor

type TerminalLimit :: PRO k VOID -> PRO k UNIT
data TerminalLimit d a b where
  TerminalLimit :: forall d a. a ~> TerminalObject -> TerminalLimit d a U

instance (HasTerminalObject k) => Profunctor (TerminalLimit (d :: PRO k VOID)) where
  dimap = dimapRep
  r \\ TerminalLimit f = r \\ f
instance (HasTerminalObject k) => Representable (TerminalLimit (d :: PRO k VOID)) where
  type TerminalLimit d % U = TerminalObject
  index (TerminalLimit f) = f
  tabulate = TerminalLimit
  repMap Unit = id

instance (HasTerminalObject k) => HasLimits (Unweighted :: PRO UNIT VOID) k where
  type Limit Unweighted d = TerminalLimit d
  limit (TerminalLimit f) = f // Rift \(TerminalProfunctor' _ o) -> tabulate (case o of {} . f)
  limitInv Rift{} = TerminalLimit terminate

type ProductLimit :: PRO k (COPRODUCT UNIT UNIT) -> PRO k UNIT
data ProductLimit d a b where
  ProductLimit :: forall d a. a ~> ProductLimit d % U -> ProductLimit d a U

instance (HasBinaryProducts k, Representable d) => Profunctor (ProductLimit d :: PRO k UNIT) where
  dimap = dimapRep
  r \\ (ProductLimit f) = r \\ f
instance (HasBinaryProducts k, Representable d) => Representable (ProductLimit d :: PRO k UNIT) where
  type ProductLimit d % U = (d % L U) && (d % R U)
  index (ProductLimit f) = f
  tabulate = ProductLimit
  repMap Unit = (***) @_ @(d % L U) @(d % R U) (repMap @d (InjL Unit)) (repMap @d (InjR Unit))

instance (HasBinaryProducts k) => HasLimits (Unweighted :: PRO UNIT (COPRODUCT UNIT UNIT)) k where
  type Limit Unweighted d = ProductLimit d
  limit (ProductLimit @d f) = f // Rift \(TerminalProfunctor' _ o) -> tabulate $ choose @_ @d o . f
  limitInv (Rift k) =
    let l = k (TerminalProfunctor' Unit (InjL Unit))
        r = k (TerminalProfunctor' Unit (InjR Unit))
    in ProductLimit $ index l &&& index r

choose
  :: forall k (d :: PRO k (COPRODUCT UNIT UNIT)) b
   . (HasBinaryProducts k, Representable d)
  => Obj b
  -> ((d % L U) && (d % R U)) ~> (d % b)
choose b = withRepCod @d @(L U) $ withRepCod @d @(R U) $ case b of
  (InjL Unit) -> fst @(d % L U) @(d % R U)
  (InjR Unit) -> snd @(d % L U) @(d % R U)

newtype End d = End {getEnd :: forall a b. a ~> b -> d % '(OP a, b)}

type EndLimit :: PRO Type (OPPOSITE k, k) -> PRO Type UNIT
data EndLimit d a b where
  EndLimit :: forall d a. (a -> End d) -> EndLimit d a U

instance (Representable d) => Profunctor (EndLimit (d :: PRO Type (OPPOSITE k, k))) where
  dimap = dimapRep
  r \\ EndLimit f = r \\ f
instance (Representable d) => Representable (EndLimit (d :: PRO Type (OPPOSITE k, k))) where
  type EndLimit d % U = End d
  index (EndLimit f) = f
  tabulate = EndLimit
  repMap Unit = id

type Hom :: PRO UNIT (OPPOSITE k, k)
data Hom a b where
  Hom :: (Ob ab) => UN OP (Fst ab) ~> Snd ab -> Hom U ab
instance (CategoryOf k) => Profunctor (Hom :: PRO UNIT (OPPOSITE k, k)) where
  dimap Unit (Op l :**: r) (Hom f) = Hom (r . f . l) \\ l \\ r
  r \\ Hom f = r \\ f

instance (CategoryOf k) => HasLimits (Hom :: PRO UNIT (OPPOSITE k, k)) Type where
  type Limit Hom d = EndLimit d
  limit (EndLimit @d f) = f // Rift \(Hom k) -> tabulate @d (\a -> getEnd (f a) k)
  limitInv (Rift n) = EndLimit \a -> End \x -> index (n (Hom x)) a \\ x
