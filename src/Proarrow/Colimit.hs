{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Colimit where

import Data.Function (($))
import Data.Kind (Constraint, Type)

import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), IsLR (..))
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), lft, rgt)
import Proarrow.Colimit.Copower (Copowered (..))
import Proarrow.Colimit.Initial (HasInitialObject (..), initiate)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), lmap, (//), (:~>), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..), corepUniv, withObCorep)
import Proarrow.Profunctor.HaskValue (HaskValue (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))

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

type O1 = L '()
type O2 = R '()
type At1 d = d %% O1
type At2 d = d %% O2

data family CoproductColimit :: k +-> COPRODUCT () () -> () +-> k
instance (HasBinaryCoproducts k, Corepresentable d) => FunctorForRep (CoproductColimit d :: () +-> k) where
  type CoproductColimit d @ '() = At1 d || At2 d
  fmap Unit = withObCorep @d @O1 $ withObCorep @d @O2 $ withObCoprod @_ @(At1 d) @(At2 d) id

instance (HasBinaryCoproducts k) => HasColimits (Unweighted :: () +-> COPRODUCT () ()) k where
  type Colimit Unweighted d = Corep (CoproductColimit d)
  colimit @d (TerminalProfunctor @o :.: Corep f) =
    withObCorep @d @O1 $
      withObCorep @d @O2 $
        lrCase @o
          (cotabulate (f . lft @_ @(At1 d) @(At2 d)))
          (cotabulate (f . rgt @_ @(At1 d) @(At2 d)))
  colimitUniv n p =
    p //
      let l = n (TerminalProfunctor @O1 :.: p)
          r = n (TerminalProfunctor @O2 :.: p)
      in Corep $ coindex l ||| coindex r

data family CopowerLimit :: Type -> k +-> () -> () +-> k
instance (Corepresentable d, Copowered Type k) => FunctorForRep (CopowerLimit n d :: () +-> k) where
  type CopowerLimit n d @ '() = n *. (d %% '())
  fmap Unit = withObCorep @d @'() $ withObCopower @Type @k @(d %% '()) @n id
instance (Copowered Type k) => HasColimits (HaskValue n :: () +-> ()) k where
  type Colimit (HaskValue n) d = Corep (CopowerLimit n d)
  colimit @d (HaskValue n :.: Corep f) = withObCorep @d @'() $ cotabulate $ uncopower f n
  colimitUniv @d m p = withObCorep @d @'() $ Corep (copower \n -> coindex (m (HaskValue n :.: p))) \\ p

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

instance (FunctorForRep f) => HasColimits (Rep f) k where
  type Colimit (Rep f) d = Corep f :.: d
  colimit (Rep f :.: (Corep g :.: d)) = lmap (g . f) d
  colimitUniv n p = p // corepUniv :.: n (repUniv :.: p)