{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Colimit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Adjunction (Adjunction (..), unit')
import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), (:++:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , lmap
  , rmap
  , src
  , tgt
  , (//)
  , (:~>)
  , type (+->)
  )
import Proarrow.Functor (Functor)
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft, rgt)
import Proarrow.Object.Copower (Copowered (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.HaskValue (HaskValue (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable
  ( CorepStar (..)
  , RepCostar (..)
  , Representable (..)
  , dimapRep
  , repObj
  , trivialRep
  , withRepOb
  )
import Proarrow.Profunctor.Star (Star)
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))

type Unweighted = TerminalProfunctor

class (Representable (Colimit j d)) => IsRepresentableColimit j d
instance (Representable (Colimit j d)) => IsRepresentableColimit j d

-- | profunctor-weighted colimits
type HasColimits :: forall {i} {a}. a +-> i -> Kind -> Constraint
class (Profunctor j, forall (d :: i +-> k). (Representable d) => IsRepresentableColimit j d) => HasColimits (j :: a +-> i) k where
  type Colimit (j :: a +-> i) (d :: i +-> k) :: a +-> k
  colimit :: (Representable (d :: i +-> k)) => d :.: j :~> Colimit j d

  -- Note: can't simplify this to Colimit j d :~> d :.: j because j is not necessarily representable.
  colimitUniv :: (Representable (d :: i +-> k), Representable p) => (d :.: j :~> p) -> Colimit j d :~> p
  colimitUniv @d @p n c =
    c // case h c of
      (ic, p) ->
        tabulate @p
          ( unRepCostar
              (colimitUniv' @j @k @d (\(j :.: RepCostar f) -> j // RepCostar (f . index (n (tabulate (repMap @d (src j)) :.: j)))) p)
              . ic
          )
    where
      h :: (Ob b) => Colimit j d a1 b -> (a1 ~> Colimit j d % b, RepCostar p b (p % b))
      h c' = (index c', RepCostar (repMap @p (tgt c')))

  -- | The same as `colimitUniv`, but with `Corepresentable`s, which is easier to work with.
  colimitUniv'
    :: (Representable (d :: i +-> k), Corepresentable p) => (j :.: p :~> RepCostar d) -> p b c -> RepCostar (Colimit j d) b c
  colimitUniv' @d @p @b n p =
    p //
      RepCostar
        ( coindex p
            . unCorepStar
              ( colimitUniv @j @k @d @(CorepStar p)
                  (\(d :.: j) -> j // CorepStar (unRepCostar (n (j :.: cotabulate @p (corepMap @p (tgt j)))) . index d))
                  (trivialRep @(Colimit j d) @b)
              )
        )

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
  InitialLimit :: forall {k} d a. a ~> InitialLimit d % '() -> InitialLimit (d :: VOID +-> k) a '()
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
  colimitUniv' _ p = p // RepCostar initiate

type CoproductColimit :: COPRODUCT () () +-> k -> () +-> k
data CoproductColimit d a b where
  CoproductColimit :: forall d a. a ~> CoproductColimit d % '() -> CoproductColimit d a '()
instance (HasBinaryCoproducts k, Representable d) => Profunctor (CoproductColimit d :: () +-> k) where
  dimap = dimapRep
  r \\ CoproductColimit f = r \\ f
instance (HasBinaryCoproducts k, Representable d) => Representable (CoproductColimit d :: () +-> k) where
  type CoproductColimit d % '() = (d % L '()) || (d % R '())
  index (CoproductColimit f) = f
  tabulate = CoproductColimit
  repMap Unit = (+++) @_ @(d % L '()) @(d % R '()) (repMap @d (InjL Unit)) (repMap @d (InjR Unit))

instance (HasBinaryCoproducts k) => HasColimits (Unweighted :: () +-> COPRODUCT () ()) k where
  type Colimit Unweighted d = CoproductColimit d
  colimit @d (d :.: TerminalProfunctor' b Unit) = CoproductColimit (cochoose @k @d b . index d)
  colimitUniv' n p =
    p // case (n (TerminalProfunctor' (InjL Unit) Unit :.: p), n (TerminalProfunctor' (InjR Unit) Unit :.: p)) of
      (RepCostar l, RepCostar r) -> RepCostar (l ||| r)

cochoose
  :: forall k (d :: COPRODUCT () () +-> k) b
   . (HasBinaryCoproducts k, Representable d)
  => Obj b
  -> (d % b) ~> ((d % L '()) || (d % R '()))
cochoose b = withRepOb @d @(L '()) $ withRepOb @d @(R '()) $ case b of
  (InjL Unit) -> lft @_ @(d % L '()) @(d % R '())
  (InjR Unit) -> rgt @_ @(d % L '()) @(d % R '())

type CopowerLimit :: Type -> () +-> k -> () +-> k
data CopowerLimit n d a b where
  CopowerLimit :: forall n d a. (Ob n) => (a ~> CopowerLimit n d % '()) -> CopowerLimit n d a '()
instance (Representable d, Copowered k) => Profunctor (CopowerLimit n d :: () +-> k) where
  dimap = dimapRep
  r \\ CopowerLimit f = r \\ f
instance (Representable d, Copowered k) => Representable (CopowerLimit n d :: () +-> k) where
  type CopowerLimit n d % '() = n *. (d % '())
  index (CopowerLimit f) = f
  tabulate = CopowerLimit
  repMap Unit = withObCopower @k @(d % '()) @n id \\ repObj @d @'()

instance (Copowered k) => HasColimits (HaskValue n :: () +-> ()) k where
  type Colimit (HaskValue n) d = CopowerLimit n d
  colimit @d (d :.: HaskValue n) = withObCopower @k @(d % '()) @n (CopowerLimit (uncopower id n . index d)) \\ repObj @d @'()
  colimitUniv' @d m p = RepCostar (copower (\n -> case m (HaskValue n :.: p) of RepCostar f -> f)) \\ p \\ repObj @d @'()

instance (CategoryOf j) => HasColimits (Id :: CAT j) k where
  type Colimit Id d = d
  colimit (d :.: Id f) = rmap f d
  colimitUniv' n p = n (Id id :.: p) \\ p

instance (Corepresentable j2, HasColimits j1 k, HasColimits j2 k) => HasColimits (j1 :.: j2) k where
  type Colimit (j1 :.: j2) d = Colimit j2 (Colimit j1 d)
  colimit (d :.: (j1 :.: j2)) = colimit @j2 @k (colimit @j1 @k (d :.: j1) :.: j2)
  colimitUniv' @d n = colimitUniv' @j2 @k @(Colimit j1 d) (colimitUniv' @j1 @k @d (\(j1 :.: (j2 :.: p1)) -> n ((j1 :.: j2) :.: p1)))

instance (Functor j) => HasColimits (Star j) k where
  type Colimit (Star j) d = d :.: Star j
  colimit = id
  colimitUniv n = n