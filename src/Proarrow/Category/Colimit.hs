{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Colimit where

import Data.Either (Either(..))
import Data.Function (($))
import Data.Kind (Type, Constraint)
import Data.Void (Void)

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>), (:~>), CategoryOf)
import Proarrow.Category.Instance.Coproduct ((:++:)(..))
import Proarrow.Category.Instance.Unit (Unit(..))
import Proarrow.Category.Instance.Zero ()
import Proarrow.Profunctor.Corepresentable (Corepresentable(..), withCorepCod)
import Proarrow.Profunctor.Ran (type (|>), Ran(..))
import Proarrow.Profunctor.Codiscrete (Codiscrete(..))
import Proarrow.Object (Obj)
import Proarrow.Object.Initial (HasInitialObject(..), initiate)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..), left, right)

type Unweighted = Codiscrete

type HasColimits :: PRO i a -> Type -> Constraint
class HasColimits (j :: PRO i a) k where
  -- Colimit has to be Corepresentable too
  type Colimit (j :: PRO i a) (d :: PRO i k) :: PRO a k
  colimit :: Corepresentable (d :: PRO i k) => Colimit j d :~> j |> d
  colimitInv :: Corepresentable (d :: PRO i k) => j |> d :~> Colimit j d


type InitialLimit :: PRO Void k -> PRO () k
data InitialLimit d a b where
  InitialLimit :: forall d a. Ob a => InitialObject ~> a -> InitialLimit d '() a

instance HasInitialObject k => HasColimits (Unweighted :: PRO Void ()) k where
  type Colimit Unweighted d = InitialLimit d
  colimit (InitialLimit @d f) = Ran \(Codiscrete o _) -> cotabulate $ f . case o of
  colimitInv Ran{} = InitialLimit initiate


type CoproductColimit :: PRO (Either () ()) k -> PRO () k
data CoproductColimit d a b where
  CoproductColimit :: forall d b. Ob b => ((d %% Left '()) || (d %% Right '())) ~> b -> CoproductColimit d '() b

instance CategoryOf k => Profunctor (CoproductColimit d :: PRO () k) where
  dimap Unit r (CoproductColimit f) = CoproductColimit (r . f) \\ r
  r \\ (CoproductColimit f) = r \\ f

instance HasBinaryCoproducts k => HasColimits (Unweighted :: PRO (Either () ()) ()) k where
  type Colimit Unweighted d = CoproductColimit d
  colimit (CoproductColimit @d f) = Ran \(Codiscrete o _) -> cotabulate $ f . cochoose @_ @d o
  colimitInv (Ran k) =
    let l = k (Codiscrete (L Unit) Unit)
        r = k (Codiscrete (R Unit) Unit)
    in CoproductColimit $ coindex l ||| coindex r

cochoose
  :: forall k (d :: PRO (Either () ()) k) b
  .  (HasBinaryCoproducts k, Corepresentable d)
  => Obj b -> (d %% b) ~> ((d %% Left '()) || (d %% Right '()))
cochoose b = withCorepCod @d @(Left '()) $ withCorepCod @d @(Right '()) $ case b of
  (L Unit) -> left @(d %% Left '()) @(d %% Right '())
  (R Unit) -> right @(d %% Left '()) @(d %% Right '())