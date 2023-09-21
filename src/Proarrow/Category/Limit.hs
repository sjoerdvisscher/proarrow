{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Limit where

import Data.Either (Either(..))
import Data.Function (($))
import Data.Kind (Type, Constraint)
import Data.Void (Void)

import Proarrow.Category.Instance.Coproduct ((:++:)(..))
import Proarrow.Category.Instance.Unit (Unit(..))
import Proarrow.Category.Instance.Zero ()
import Proarrow.Core (PRO, (:~>), Category (..), Profunctor(..), type (~>), (//), CategoryOf)
import Proarrow.Profunctor.Codiscrete (Codiscrete(..))
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

type Unweighted = Codiscrete


type TerminalLimit :: PRO k Void -> PRO k ()
data TerminalLimit d a b where
  TerminalLimit :: forall d a. a ~> TerminalObject -> TerminalLimit d a '()

instance HasTerminalObject k => HasLimits (Unweighted :: PRO () Void) k where
  type Limit Unweighted d = TerminalLimit d
  limit (TerminalLimit @d f) = f // Rift \(Codiscrete _ o) -> tabulate (case o of . f)
  limitInv Rift{} = TerminalLimit terminate


type ProductLimit :: PRO k (Either () ()) -> PRO k ()
data ProductLimit d a b where
  ProductLimit :: forall d a. a ~> ((d % Left '()) && (d % Right '())) -> ProductLimit d a '()

instance CategoryOf k => Profunctor (ProductLimit d :: PRO k ()) where
  dimap l Unit (ProductLimit f) = ProductLimit (f . l) \\ l
  r \\ (ProductLimit f) = r \\ f

instance (HasBinaryProducts k, Representable d) => Representable (ProductLimit d :: PRO k ()) where
  type ProductLimit d % '() = (d % Left '()) && (d % Right '())
  index (ProductLimit f) = f
  tabulate = ProductLimit
  repMap Unit = repMap @d (L Unit) *** repMap @d (R Unit)

instance HasBinaryProducts k => HasLimits (Unweighted :: PRO () (Either () ())) k where
  type Limit Unweighted d = ProductLimit d
  limit (ProductLimit @d f) = f // Rift \(Codiscrete _ o) -> tabulate $ choose @_ @d o . f
  limitInv (Rift k) =
    let l = k (Codiscrete Unit (L Unit))
        r = k (Codiscrete Unit (R Unit))
    in ProductLimit $ index l &&& index r

choose
  :: forall k (d :: PRO k (Either () ())) b
  .  (HasBinaryProducts k, Representable d)
  => Obj b -> ((d % Left '()) && (d % Right '())) ~> (d % b)
choose b = withRepCod @d @(Left '()) $ withRepCod @d @(Right '()) $ case b of
  (L Unit) -> fst @(d % Left '()) @(d % Right '())
  (R Unit) -> snd @(d % Left '()) @(d % Right '())