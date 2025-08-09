{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Colimit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), type (:++:) (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), lmap, rmap, (//), (:~>), type (+->))
import Proarrow.Functor (Functor)
import Proarrow.Object (Obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft, rgt)
import Proarrow.Object.Copower (Copowered (..))
import Proarrow.Object.Initial (HasInitialObject (..), initiate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepObj, dimapCorep, withCorepOb)
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.HaskValue (HaskValue (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Star (Star (..))
import Proarrow.Profunctor.Terminal (TerminalProfunctor (TerminalProfunctor'))

type Unweighted = TerminalProfunctor

class (Corepresentable (Colimit j d)) => IsCorepresentableColimit j d
instance (Corepresentable (Colimit j d)) => IsCorepresentableColimit j d

-- | profunctor-weighted colimits
type HasColimits :: forall {i} {a}. a +-> i -> Kind -> Constraint
class
  (Profunctor j, forall (d :: k +-> i). (Corepresentable d) => IsCorepresentableColimit j d) =>
  HasColimits (j :: a +-> i) k
  where
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
  colimit = \case {}
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
    p //
      let l = n (TerminalProfunctor' (InjL Unit) Unit :.: p)
          r = n (TerminalProfunctor' (InjR Unit) Unit :.: p)
      in CoproductColimit $ coindex l ||| coindex r

cochoose
  :: forall k (d :: k +-> COPRODUCT () ()) b
   . (HasBinaryCoproducts k, Corepresentable d)
  => Obj b
  -> (d %% b) ~> ((d %% L '()) || (d %% R '()))
cochoose b = withCorepOb @d @(L '()) $ withCorepOb @d @(R '()) $ case b of
  (InjL Unit) -> lft @_ @(d %% L '()) @(d %% R '())
  (InjR Unit) -> rgt @_ @(d %% L '()) @(d %% R '())

type CopowerLimit :: Type -> k +-> () -> k +-> ()
data CopowerLimit n d a b where
  CopowerLimit :: forall n d b. (Ob n) => (CopowerLimit n d %% '() ~> b) -> CopowerLimit n d '() b
instance (Corepresentable d, Copowered Type k) => Profunctor (CopowerLimit n d :: k +-> ()) where
  dimap = dimapCorep
  r \\ CopowerLimit f = r \\ f
instance (Corepresentable d, Copowered Type k) => Corepresentable (CopowerLimit n d :: k +-> ()) where
  type CopowerLimit n d %% '() = n *. (d %% '())
  coindex (CopowerLimit f) = f
  cotabulate = CopowerLimit
  corepMap Unit = withObCopower @Type @k @(d %% '()) @n id \\ corepObj @d @'()
instance (Copowered Type k) => HasColimits (HaskValue n :: () +-> ()) k where
  type Colimit (HaskValue n) d = CopowerLimit n d
  colimit @d (HaskValue n :.: CopowerLimit f) = cotabulate (uncopower f n) \\ corepObj @d @'()
  colimitUniv @d m p = CopowerLimit (copower \n -> coindex (m (HaskValue n :.: p))) \\ p \\ corepObj @d @'()

data Coend d where
  Coend :: a ~> b -> d %% '(OP b, a) -> Coend d

type CoendLimit :: Type +-> (OPPOSITE k, k) -> Type +-> ()
data CoendLimit d a b where
  CoendLimit :: forall d b. (Coend d -> b) -> CoendLimit d '() b

instance (Corepresentable d) => Profunctor (CoendLimit (d :: Type +-> (OPPOSITE k, k))) where
  dimap = dimapCorep
  r \\ CoendLimit f = r \\ f
instance (Corepresentable d) => Corepresentable (CoendLimit (d :: Type +-> (OPPOSITE k, k))) where
  type CoendLimit d %% '() = Coend d
  coindex (CoendLimit f) = f
  cotabulate = CoendLimit
  corepMap Unit = id

type Hom :: () +-> (OPPOSITE k, k)
data Hom a b where
  Hom :: a ~> b -> Hom '(OP b, a) '()
instance (CategoryOf k) => Profunctor (Hom :: () +-> (OPPOSITE k, k)) where
  dimap (Op l :**: r) Unit (Hom f) = Hom (l . f . r) \\ l \\ r
  r \\ Hom f = r \\ f

instance (CategoryOf k) => HasColimits (Hom :: () +-> (OPPOSITE k, k)) Type where
  type Colimit Hom d = CoendLimit d
  colimit (Hom f :.: CoendLimit g) = f // cotabulate (\d -> g (Coend f d))
  colimitUniv n p = p // CoendLimit \(Coend f d) -> coindex (n (Hom f :.: p)) d

instance (CategoryOf j) => HasColimits (Id :: CAT j) k where
  type Colimit Id d = d
  colimit (Id f :.: d) = lmap f d
  colimitUniv n p = n (Id id :.: p) \\ p

instance (Corepresentable j2, HasColimits j1 k, HasColimits j2 k) => HasColimits (j1 :.: j2) k where
  type Colimit (j1 :.: j2) d = Colimit j2 (Colimit j1 d)
  colimit @d ((j1 :.: j2) :.: c) = colimit @j1 @k @d (j1 :.: colimit @j2 @k @(Colimit j1 d) (j2 :.: c))
  colimitUniv @d n = colimitUniv @j2 @k @(Colimit j1 d) (colimitUniv @j1 @k @d (\(j1 :.: (j2 :.: p')) -> n ((j1 :.: j2) :.: p')))

instance (Functor j) => HasColimits (Star j) k where
  type Colimit (Star j) d = Costar j :.: d
  colimit (Star f :.: (Costar g :.: d)) = lmap (g . f) d
  colimitUniv n p = p // Costar id :.: n (Star id :.: p)
