{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Colimit where

import Data.Function (($))
import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT, COLLAGE(..), pattern InjL, pattern InjR)
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Core (CategoryOf (..), Kind, Profunctor (..), Promonad (..), rmap, (//), (:~>), type (+->))
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft, rgt)
import Proarrow.Object.Initial (HasInitialObject (..), initiate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep, withCorepCod)
import Proarrow.Profunctor.Terminal (TerminalProfunctor (TerminalProfunctor'))

type Unweighted = TerminalProfunctor

class (Corepresentable (Colimit j d)) => IsCorepresentableColimit j d
instance (Corepresentable (Colimit j d)) => IsCorepresentableColimit j d

-- | profunctor-weighted colimits
type HasColimits :: forall {i} {a}. a +-> i -> Kind -> Constraint
class (forall (d :: k +-> i). (Corepresentable d) => IsCorepresentableColimit j d) => HasColimits (j :: a +-> i) k where
  type Colimit (j :: a +-> i) (d :: k +-> i) :: k +-> a
  colimit :: (Corepresentable (d :: k +-> i)) => j :.: Colimit j d :~> d
  colimitUniv :: (Corepresentable (d :: k +-> i), Profunctor p) => (j :.: p :~> d) -> p :~> Colimit j d

leftAdjointPreservesColimits
  :: forall {k} {k'} {i} {a} (f :: k' +-> k) g (d :: k +-> i) (j :: a +-> i)
   . (Adjunction f g, Corepresentable d, Corepresentable f, HasColimits j k, HasColimits j k')
  => Colimit j (d :.: f) :~> Colimit j d :.: f
leftAdjointPreservesColimits colim =
  colim // case unit @f @g of
    g :.: f ->
      colimitUniv @j @k @d
        (\(j :.: (colim' :.: g')) -> case colimit @j @k' @(d :.: f) (j :.: colim') of d :.: f' -> rmap (counit (f' :.: g')) d)
        (colim :.: g)
        :.: f

leftAdjointPreservesColimitsInv
  :: forall {k} {k'} {i} {a} (f :: k' +-> k) (d :: k +-> i) (j :: a +-> i)
   . (Corepresentable d, Corepresentable f, HasColimits j k, HasColimits j k')
  => Colimit j d :.: f :~> Colimit j (d :.: f)
leftAdjointPreservesColimitsInv = colimitUniv @j @k' @(d :.: f) (\(j :.: (colim :.: f)) -> colimit (j :.: colim) :.: f)

type InitialLimit :: k +-> VOID -> k +-> ()
data InitialLimit d a b where
  InitialLimit :: forall d a. InitialObject ~> a -> InitialLimit d '() a

instance (HasInitialObject k) => Profunctor (InitialLimit (d :: k +-> VOID)) where
  dimap = dimapCorep
  r \\ InitialLimit f = r \\ f
instance (HasInitialObject k) => Corepresentable (InitialLimit (d :: k +-> VOID)) where
  type InitialLimit d %% '() = InitialObject
  coindex (InitialLimit f) = f
  cotabulate = InitialLimit
  corepMap Unit = id
instance (HasInitialObject k) => HasColimits (Unweighted :: () +-> VOID) k where
  type Colimit Unweighted d = InitialLimit d
  colimit = \case
  colimitUniv _ p = p // InitialLimit initiate

type CoproductColimit :: k +-> COPRODUCT () () -> k +-> ()
data CoproductColimit d a b where
  CoproductColimit :: forall d b. ((d %% L '()) || (d %% R '())) ~> b -> CoproductColimit d '() b

instance (CategoryOf k) => Profunctor (CoproductColimit d :: k +-> ()) where
  dimap Unit r (CoproductColimit f) = CoproductColimit (r . f) \\ r
  r \\ (CoproductColimit f) = r \\ f

instance (HasBinaryCoproducts k, Corepresentable d) => Corepresentable (CoproductColimit d :: k +-> ()) where
  type CoproductColimit d %% '() = (d %% L '()) || (d %% R '())
  coindex (CoproductColimit f) = f
  cotabulate = CoproductColimit
  corepMap Unit = (+++) @_ @(d %% L '()) @(d %% R '()) (corepMap @d (InjL Unit)) (corepMap @d (InjR Unit))

instance (HasBinaryCoproducts k) => HasColimits (Unweighted :: () +-> COPRODUCT () ()) k where
  type Colimit Unweighted d = CoproductColimit d
  colimit (TerminalProfunctor' o _ :.: CoproductColimit @d f) = o // cotabulate $ f . cochoose @_ @d o
  colimitUniv n p =
    p
      // let l = n (TerminalProfunctor' (InjL Unit) Unit :.: p)
             r = n (TerminalProfunctor' (InjR Unit) Unit :.: p)
         in CoproductColimit $ coindex l ||| coindex r

cochoose
  :: forall k (d :: k +-> COPRODUCT () ()) b
   . (HasBinaryCoproducts k, Corepresentable d)
  => Obj b
  -> (d %% b) ~> ((d %% L '()) || (d %% R '()))
cochoose b = withCorepCod @d @(L '()) $ withCorepCod @d @(R '()) $ case b of
  (InjL Unit) -> lft @_ @(d %% L '()) @(d %% R '())
  (InjR Unit) -> rgt @_ @(d %% L '()) @(d %% R '())
