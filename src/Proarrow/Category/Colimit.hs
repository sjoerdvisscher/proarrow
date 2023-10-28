{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Colimit where

import Data.Function (($))
import Data.Kind (Type, Constraint)

import Proarrow.Core (PRO, CategoryOf(..), Promonad(..), Profunctor(..), (:~>), CategoryOf)
import Proarrow.Category.Instance.Coproduct (COPRODUCT(..), (:++:)(..))
import Proarrow.Category.Instance.Unit (UNIT(..), Unit(..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Profunctor.Corepresentable (Corepresentable(..), withCorepCod)
import Proarrow.Profunctor.Ran (type (|>), Ran(..))
import Proarrow.Profunctor.Terminal (TerminalProfunctor(TerminalProfunctor'))
import Proarrow.Object (Obj)
import Proarrow.Object.Initial (HasInitialObject(..), initiate)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..), lft, rgt)

type Unweighted = TerminalProfunctor

type HasColimits :: PRO i a -> Type -> Constraint
class HasColimits (j :: PRO i a) k where
  -- Colimit has to be Corepresentable too
  type Colimit (j :: PRO i a) (d :: PRO i k) :: PRO a k
  colimit :: Corepresentable (d :: PRO i k) => Colimit j d :~> j |> d
  colimitInv :: Corepresentable (d :: PRO i k) => j |> d :~> Colimit j d


type InitialLimit :: PRO VOID k -> PRO UNIT k
data InitialLimit d a b where
  InitialLimit :: forall d a. Ob a => InitialObject ~> a -> InitialLimit d U a

instance HasInitialObject k => HasColimits (Unweighted :: PRO VOID UNIT) k where
  type Colimit Unweighted d = InitialLimit d
  colimit (InitialLimit @d f) = Ran \(TerminalProfunctor' o _) -> cotabulate $ f . case o of
  colimitInv Ran{} = InitialLimit initiate


type CoproductColimit :: PRO (COPRODUCT UNIT UNIT) k -> PRO UNIT k
data CoproductColimit d a b where
  CoproductColimit :: forall d b. Ob b => ((d %% L U) || (d %% R U)) ~> b -> CoproductColimit d U b

instance CategoryOf k => Profunctor (CoproductColimit d :: PRO UNIT k) where
  dimap Unit r (CoproductColimit f) = CoproductColimit (r . f) \\ r
  r \\ (CoproductColimit f) = r \\ f

instance HasBinaryCoproducts k => HasColimits (Unweighted :: PRO (COPRODUCT UNIT UNIT) UNIT) k where
  type Colimit Unweighted d = CoproductColimit d
  colimit (CoproductColimit @d f) = Ran \(TerminalProfunctor' o _) -> cotabulate $ f . cochoose @_ @d o
  colimitInv (Ran k) =
    let l = k (TerminalProfunctor' (InjL Unit) Unit)
        r = k (TerminalProfunctor' (InjR Unit) Unit)
    in CoproductColimit $ coindex l ||| coindex r

cochoose
  :: forall k (d :: PRO (COPRODUCT UNIT UNIT) k) b
  .  (HasBinaryCoproducts k, Corepresentable d)
  => Obj b -> (d %% b) ~> ((d %% L U) || (d %% R U))
cochoose b = withCorepCod @d @(L U) $ withCorepCod @d @(R U) $ case b of
  (InjL Unit) -> lft @(d %% L U) @(d %% R U)
  (InjR Unit) -> rgt @(d %% L U) @(d %% R U)