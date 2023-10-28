{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Limit where

import Data.Function (($))
import Data.Kind (Type, Constraint)

import Proarrow.Category.Instance.Coproduct (COPRODUCT(..), (:++:)(..))
import Proarrow.Category.Instance.Unit (UNIT(..), Unit(..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Core (PRO, (:~>), CategoryOf (..), Promonad(..), Profunctor(..), (//), CategoryOf)
import Proarrow.Profunctor.Terminal (TerminalProfunctor(TerminalProfunctor'))
import Proarrow.Profunctor.Representable (Representable (..), withRepCod)
import Proarrow.Profunctor.Rift (type (<|), Rift (..))
import Proarrow.Object (Obj)
import Proarrow.Object.Terminal (HasTerminalObject(..), terminate)
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..), fst, snd)

-- profunctor-weighted limits
type HasLimits :: PRO a i -> Type -> Constraint
class HasLimits (j :: PRO a i) k where
  -- Limit has to be Representable too
  type Limit (j :: PRO a i) (d :: PRO k i) :: PRO k a
  limit :: Representable (d :: PRO k i) => Limit j d :~> d <| j
  limitInv :: Representable (d :: PRO k i) => d <| j :~> Limit j d

type Unweighted = TerminalProfunctor


type TerminalLimit :: PRO k VOID -> PRO k UNIT
data TerminalLimit d a b where
  TerminalLimit :: forall d a. a ~> TerminalObject -> TerminalLimit d a U

instance HasTerminalObject k => HasLimits (Unweighted :: PRO UNIT VOID) k where
  type Limit Unweighted d = TerminalLimit d
  limit (TerminalLimit @d f) = f // Rift \(TerminalProfunctor' _ o) -> tabulate (case o of . f)
  limitInv Rift{} = TerminalLimit terminate


type ProductLimit :: PRO k (COPRODUCT UNIT UNIT) -> PRO k UNIT
data ProductLimit d a b where
  ProductLimit :: forall d a. a ~> ((d % L U) && (d % R U)) -> ProductLimit d a U

instance CategoryOf k => Profunctor (ProductLimit d :: PRO k UNIT) where
  dimap l Unit (ProductLimit f) = ProductLimit (f . l) \\ l
  r \\ (ProductLimit f) = r \\ f

instance (HasBinaryProducts k, Representable d) => Representable (ProductLimit d :: PRO k UNIT) where
  type ProductLimit d % U = (d % L U) && (d % R U)
  index (ProductLimit f) = f
  tabulate = ProductLimit
  repMap Unit = repMap @d (InjL Unit) *** repMap @d (InjR Unit)

instance HasBinaryProducts k => HasLimits (Unweighted :: PRO UNIT (COPRODUCT UNIT UNIT)) k where
  type Limit Unweighted d = ProductLimit d
  limit (ProductLimit @d f) = f // Rift \(TerminalProfunctor' _ o) -> tabulate $ choose @_ @d o . f
  limitInv (Rift k) =
    let l = k (TerminalProfunctor' Unit (InjL Unit))
        r = k (TerminalProfunctor' Unit (InjR Unit))
    in ProductLimit $ index l &&& index r

choose
  :: forall k (d :: PRO k (COPRODUCT UNIT UNIT)) b
  .  (HasBinaryProducts k, Representable d)
  => Obj b -> ((d % L U) && (d % R U)) ~> (d % b)
choose b = withRepCod @d @(L U) $ withRepCod @d @(R U) $ case b of
  (InjL Unit) -> fst @(d % L U) @(d % R U)
  (InjR Unit) -> snd @(d % L U) @(d % R U)