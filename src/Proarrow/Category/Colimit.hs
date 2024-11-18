{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Colimit where

import Data.Function (($))
import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction (..), unit')
import Proarrow.Category.Instance.Coproduct (COLLAGE (..), COPRODUCT, pattern InjL, pattern InjR)
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Core (CategoryOf (..), Kind, Profunctor (..), Promonad (..), lmap, src, (//), (:~>), type (+->))
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft, rgt)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep, withRepObj)
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))

type Unweighted = TerminalProfunctor

class (Representable (Colimit j d)) => IsRepresentableColimit j d
instance (Representable (Colimit j d)) => IsRepresentableColimit j d

-- | profunctor-weighted colimits
type HasColimits :: forall {i} {a}. a +-> i -> Kind -> Constraint
class (forall (d :: i +-> k). (Representable d) => IsRepresentableColimit j d) => HasColimits (j :: a +-> i) k where
  type Colimit (j :: a +-> i) (d :: i +-> k) :: a +-> k
  colimit :: (Representable (d :: i +-> k)) => d :.: j :~> Colimit j d
  colimitUniv :: (Representable (d :: i +-> k), Representable p) => (d :.: j :~> p) -> Colimit j d :~> p

leftAdjointPreservesColimits
  :: forall {k} {k'} {i} {a} (f :: k +-> k') g (d :: i +-> k) (j :: a +-> i)
   . (Adjunction f g, Representable d, Representable f, Representable g, HasColimits j k, HasColimits j k')
  => f :.: Colimit j d :~> Colimit j (f :.: d)
leftAdjointPreservesColimits (f :.: colim) =
  colim // case colimitUniv @j @k @d @(g :.: Colimit j (f :.: d))
    (\(d :.: j) -> case unit' @f @g (src d) of g :.: f' -> g :.: colimit @j @k' @(f :.: d) ((f' :.: d) :.: j))
    colim of
    g :.: colim' -> lmap (counit (f :.: g)) colim'

leftAdjointPreservesColimitsInv
  :: forall {k} {k'} {i} {a} (f :: k +-> k') (d :: i +-> k) (j :: a +-> i)
   . (Representable d, Representable f, HasColimits j k, HasColimits j k')
  => Colimit j (f :.: d) :~> f :.: Colimit j d
leftAdjointPreservesColimitsInv = colimitUniv @j @k' @(f :.: d) (\((f :.: d) :.: j) -> f :.: colimit (d :.: j))

type InitialLimit :: VOID +-> k -> () +-> k
data InitialLimit d a b where
  InitialLimit :: forall {k} d a. a ~> InitialObject -> InitialLimit (d :: VOID +-> k) a '()

instance (HasInitialObject k) => Profunctor (InitialLimit (d :: VOID +-> k)) where
  dimap = dimapRep
  r \\ InitialLimit f = r \\ f
instance (HasInitialObject k) => Representable (InitialLimit (d :: VOID +-> k)) where
  type InitialLimit d % '() = InitialObject
  index (InitialLimit f) = f
  tabulate = InitialLimit
  repMap Unit = id
instance (HasInitialObject k) => HasColimits (Unweighted :: () +-> VOID) k where
  type Colimit Unweighted d = InitialLimit d
  colimit = \case {}
  colimitUniv @_ @p _ (InitialLimit f) = tabulate @p (initiate' (repMap @p Unit) . f)

type CoproductColimit :: COPRODUCT () () +-> k -> () +-> k
data CoproductColimit d a b where
  CoproductColimit :: forall d a. a ~> ((d % L '()) || (d % R '())) -> CoproductColimit d a '()

instance (HasBinaryCoproducts k, Representable d) => Profunctor (CoproductColimit d :: () +-> k) where
  dimap = dimapRep
  r \\ (CoproductColimit f) = r \\ f

instance (HasBinaryCoproducts k, Representable d) => Representable (CoproductColimit d :: () +-> k) where
  type CoproductColimit d % '() = (d % L '()) || (d % R '())
  index (CoproductColimit f) = f
  tabulate = CoproductColimit
  repMap Unit = (+++) @_ @(d % L '()) @(d % R '()) (repMap @d (InjL Unit)) (repMap @d (InjR Unit))

instance (HasBinaryCoproducts k) => HasColimits (Unweighted :: () +-> COPRODUCT () ()) k where
  type Colimit Unweighted d = CoproductColimit d
  colimit @d (d :.: TerminalProfunctor' b Unit) = CoproductColimit (cochoose @k @d b . index d)
  colimitUniv @d @p n (CoproductColimit f) =
    let l = index @p (n (tabulate @d (repMap @d (InjL Unit)) :.: TerminalProfunctor' (InjL Unit) Unit))
        r = index @p (n (tabulate @d (repMap @d (InjR Unit)) :.: TerminalProfunctor' (InjR Unit) Unit))
    in tabulate @p ((l ||| r) . f)

cochoose
  :: forall k (d :: COPRODUCT () () +-> k) b
   . (HasBinaryCoproducts k, Representable d)
  => Obj b
  -> (d % b) ~> ((d % L '()) || (d % R '()))
cochoose b = withRepObj @d @(L '()) $ withRepObj @d @(R '()) $ case b of
  (InjL Unit) -> lft @_ @(d % L '()) @(d % R '())
  (InjR Unit) -> rgt @_ @(d % L '()) @(d % R '())
