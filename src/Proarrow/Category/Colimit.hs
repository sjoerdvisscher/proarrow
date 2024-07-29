{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Colimit where

import Data.Function (($))
import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), (:++:) (..))
import Proarrow.Category.Instance.Unit (UNIT (..), Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Core (CategoryOf (..), Kind, PRO, Profunctor (..), Promonad (..), rmap, (//), (:~>))
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft, rgt)
import Proarrow.Object.Initial (HasInitialObject (..), initiate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep, withCorepCod)
import Proarrow.Profunctor.Ran (Ran (..), type (|>))
import Proarrow.Profunctor.Terminal (TerminalProfunctor (TerminalProfunctor'))

type Unweighted = TerminalProfunctor

class (Corepresentable (Colimit j d)) => IsCorepresentableColimit j d
instance (Corepresentable (Colimit j d)) => IsCorepresentableColimit j d

-- | profunctor-weighted colimits
type HasColimits :: forall {i} {a}. PRO i a -> Kind -> Constraint
class (forall (d :: PRO i k). (Corepresentable d) => IsCorepresentableColimit j d) => HasColimits (j :: PRO i a) k where
  type Colimit (j :: PRO i a) (d :: PRO i k) :: PRO a k
  colimit :: (Corepresentable (d :: PRO i k)) => Colimit j d :~> j |> d
  colimitInv :: (Corepresentable (d :: PRO i k)) => j |> d :~> Colimit j d

leftAdjointPreservesColimits
  :: forall {k} {i} {a} f g (d :: PRO i k) (j :: PRO i a)
   . (Adjunction f g, Corepresentable d, HasColimits j k)
  => j |> (d :.: f) :~> Colimit j d :.: f
leftAdjointPreservesColimits (Ran k) =
  case unit @f @g of
    g :.: f ->
      colimitInv @j @k @d (f // Ran \j -> case k j of d :.: f' -> rmap (counit (f' :.: g)) d) :.: f

leftAdjointPreservesColimitsInv
  :: forall {k} {i} {a} f g (d :: PRO i k) (j :: PRO i a)
   . (Adjunction f g, Corepresentable d, HasColimits j k)
  => Colimit j d :.: f :~> j |> (d :.: f)
leftAdjointPreservesColimitsInv (l :.: f) =
  l // f // Ran \j ->
    case unit @f @g of
      g :.: f' -> rmap (counit (f :.: g)) (case colimit @j @k @d l of Ran k -> k j) :.: f'

type InitialLimit :: PRO VOID k -> PRO UNIT k
data InitialLimit d a b where
  InitialLimit :: forall d a. InitialObject ~> a -> InitialLimit d U a

instance (HasInitialObject k) => Profunctor (InitialLimit (d :: PRO VOID k)) where
  dimap = dimapCorep
  r \\ InitialLimit f = r \\ f
instance (HasInitialObject k) => Corepresentable (InitialLimit (d :: PRO VOID k)) where
  type InitialLimit d %% U = InitialObject
  coindex (InitialLimit f) = f
  cotabulate = InitialLimit
  corepMap Unit = id
instance (HasInitialObject k) => HasColimits (Unweighted :: PRO VOID UNIT) k where
  type Colimit Unweighted d = InitialLimit d
  colimit (InitialLimit f) = f // Ran \(TerminalProfunctor' o _) -> cotabulate $ f . case o of {}
  colimitInv Ran{} = InitialLimit initiate

type CoproductColimit :: PRO (COPRODUCT UNIT UNIT) k -> PRO UNIT k
data CoproductColimit d a b where
  CoproductColimit :: forall d b. ((d %% L U) || (d %% R U)) ~> b -> CoproductColimit d U b

instance (CategoryOf k) => Profunctor (CoproductColimit d :: PRO UNIT k) where
  dimap Unit r (CoproductColimit f) = CoproductColimit (r . f) \\ r
  r \\ (CoproductColimit f) = r \\ f

instance (HasBinaryCoproducts k, Corepresentable d) => Corepresentable (CoproductColimit d :: PRO UNIT k) where
  type CoproductColimit d %% U = (d %% L U) || (d %% R U)
  coindex (CoproductColimit f) = f
  cotabulate = CoproductColimit
  corepMap Unit = (+++) @_ @(d %% L U) @(d %% R U) (corepMap @d (InjL Unit)) (corepMap @d (InjR Unit))

instance (HasBinaryCoproducts k) => HasColimits (Unweighted :: PRO (COPRODUCT UNIT UNIT) UNIT) k where
  type Colimit Unweighted d = CoproductColimit d
  colimit (CoproductColimit @d f) = f // Ran \(TerminalProfunctor' o _) -> cotabulate $ f . cochoose @_ @d o
  colimitInv (Ran k) =
    let l = k (TerminalProfunctor' (InjL Unit) Unit)
        r = k (TerminalProfunctor' (InjR Unit) Unit)
    in CoproductColimit $ coindex l ||| coindex r

cochoose
  :: forall k (d :: PRO (COPRODUCT UNIT UNIT) k) b
   . (HasBinaryCoproducts k, Corepresentable d)
  => Obj b
  -> (d %% b) ~> ((d %% L U) || (d %% R U))
cochoose b = withCorepCod @d @(L U) $ withCorepCod @d @(R U) $ case b of
  (InjL Unit) -> lft @(d %% L U) @(d %% R U)
  (InjR Unit) -> rgt @(d %% L U) @(d %% R U)
