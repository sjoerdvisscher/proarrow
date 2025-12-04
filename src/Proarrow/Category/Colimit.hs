{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Colimit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), type (:++:) (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), lmap, (//), (:~>), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object (Obj, src)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft, rgt)
import Proarrow.Object.Copower (Copowered (..))
import Proarrow.Object.Initial (HasInitialObject (..), initiate)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..), corepObj, withCorepOb)
import Proarrow.Profunctor.HaskValue (HaskValue (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable
import Proarrow.Profunctor.Terminal (TerminalProfunctor (TerminalProfunctor'))
import Proarrow.Profunctor.Wrapped (Wrapped (..))

type Unweighted = TerminalProfunctor

class (Corepresentable (Colimit j d)) => IsCorepColimit j d
instance (Corepresentable (Colimit j d)) => IsCorepColimit j d

-- | profunctor-weighted colimits
type HasColimits :: forall {i} {a}. a +-> i -> Kind -> Constraint
class (Profunctor j, forall (d :: k +-> i). (Corepresentable d) => IsCorepColimit j d) => HasColimits (j :: a +-> i) k where
  type Colimit (j :: a +-> i) (d :: k +-> i) :: k +-> a
  colimit :: (Corepresentable (d :: k +-> i)) => j :.: Colimit j d :~> d
  colimitUniv :: (Corepresentable (d :: k +-> i), Profunctor p) => (j :.: p :~> d) -> p :~> Colimit j d

mapColimit
  :: forall {i} j k p q
   . (HasColimits j k, Corepresentable p, Corepresentable q) => (p :: k +-> i) ~> q -> Colimit j p ~> Colimit j q
mapColimit (Prof n) = Prof (colimitUniv @j (n . colimit @j))

data family InitialLimit :: k +-> VOID -> () +-> k
instance (HasInitialObject k) => FunctorForRep (InitialLimit (d :: k +-> VOID)) where
  type InitialLimit d @ '() = InitialObject
  fmap Unit = id
instance (HasInitialObject k) => HasColimits (Unweighted :: () +-> VOID) k where
  type Colimit Unweighted d = Corep (InitialLimit d)
  colimit = \case {}
  colimitUniv _ p = p // Corep initiate

data family CoproductColimit :: k +-> COPRODUCT () () -> () +-> k
instance (HasBinaryCoproducts k, Corepresentable d) => FunctorForRep (CoproductColimit d :: () +-> k) where
  type CoproductColimit d @ '() = (d %% L '()) || (d %% R '())
  fmap Unit = (+++) @_ @(d %% L '()) @(d %% R '()) (corepMap @d (InjL Unit)) (corepMap @d (InjR Unit))

instance (HasBinaryCoproducts k) => HasColimits (Unweighted :: () +-> COPRODUCT () ()) k where
  type Colimit Unweighted d = Corep (CoproductColimit d)
  colimit (TerminalProfunctor' o _ :.: Corep @(CoproductColimit d) f) = o // cotabulate $ f . cochoose @_ @d o
  colimitUniv n p =
    p //
      let l = n (TerminalProfunctor' (InjL Unit) Unit :.: p)
          r = n (TerminalProfunctor' (InjR Unit) Unit :.: p)
      in Corep $ coindex l ||| coindex r

cochoose
  :: forall k (d :: k +-> COPRODUCT () ()) b
   . (HasBinaryCoproducts k, Corepresentable d)
  => Obj b
  -> (d %% b) ~> ((d %% L '()) || (d %% R '()))
cochoose b = withCorepOb @d @(L '()) $ withCorepOb @d @(R '()) $ case b of
  (InjL Unit) -> lft @_ @(d %% L '()) @(d %% R '())
  (InjR Unit) -> rgt @_ @(d %% L '()) @(d %% R '())

data family CopowerLimit :: Type -> k +-> () -> () +-> k
instance (Corepresentable d, Copowered Type k) => FunctorForRep (CopowerLimit n d :: () +-> k) where
  type CopowerLimit n d @ '() = n *. (d %% '())
  fmap Unit = withObCopower @Type @k @(d %% '()) @n id \\ corepObj @d @'()
instance (Copowered Type k) => HasColimits (HaskValue n :: () +-> ()) k where
  type Colimit (HaskValue n) d = Corep (CopowerLimit n d)
  colimit @d (HaskValue n :.: Corep f) = cotabulate (uncopower f n) \\ corepObj @d @'()
  colimitUniv @d m p = Corep (copower \n -> coindex (m (HaskValue n :.: p))) \\ p \\ corepObj @d @'()

data Coend d where
  Coend :: a ~> b -> d %% '(OP b, a) -> Coend d

data family CoendLimit :: Type +-> (OPPOSITE k, k) -> () +-> Type
instance (Corepresentable d) => FunctorForRep (CoendLimit (d :: Type +-> (OPPOSITE k, k))) where
  type CoendLimit d @ '() = Coend d
  fmap Unit = id

type Hom :: () +-> (OPPOSITE k, k)
data Hom a b where
  Hom :: a ~> b -> Hom '(OP b, a) '()
instance (CategoryOf k) => Profunctor (Hom :: () +-> (OPPOSITE k, k)) where
  dimap (Op l :**: r) Unit (Hom f) = Hom (l . f . r) \\ l \\ r
  r \\ Hom f = r \\ f

instance (CategoryOf k) => HasColimits (Hom :: () +-> (OPPOSITE k, k)) Type where
  type Colimit Hom d = Corep (CoendLimit d)
  colimit (Hom f :.: Corep g) = f // cotabulate (\d -> g (Coend f d))
  colimitUniv n p = p // Corep \(Coend f d) -> coindex (n (Hom f :.: p)) d

instance (CategoryOf j) => HasColimits (Id :: CAT j) k where
  type Colimit Id d = d
  colimit (Id f :.: d) = lmap f d
  colimitUniv n p = n (Id id :.: p) \\ p

instance (Corepresentable j2, HasColimits j1 k, HasColimits j2 k) => HasColimits (j1 :.: j2) k where
  type Colimit (j1 :.: j2) d = Colimit j2 (Colimit j1 d)
  colimit @d ((j1 :.: j2) :.: c) = colimit @j1 @k @d (j1 :.: colimit @j2 @k @(Colimit j1 d) (j2 :.: c))
  colimitUniv @d n = colimitUniv @j2 @k @(Colimit j1 d) (colimitUniv @j1 @k @d (\(j1 :.: (j2 :.: p')) -> n ((j1 :.: j2) :.: p')))

instance (Representable j) => HasColimits (Wrapped j) k where
  type Colimit (Wrapped j) d = RepCostar j :.: d
  colimit (j :.: (RepCostar g :.: d)) = lmap (g . index j) d
  colimitUniv n p = p // RepCostar (repMap @j (src p)) :.: n (trivialRep :.: p)