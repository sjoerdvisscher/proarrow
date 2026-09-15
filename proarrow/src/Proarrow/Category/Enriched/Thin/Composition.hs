{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Composition of thin profunctors. In general the arrows of a composite @p ':.:' q@ are an
-- existential over the objects of the middle category, which a 'Constraint' cannot express. This
-- module dispatches on the shape of the legs, so that the single 'ThinProfunctor' instance for
-- ':.:' never overlaps with anything: a representable leg pins the middle object down, and
-- otherwise the middle category is searched ('Search'), which needs it to be 'Enumerable' and both
-- legs to be 'DecidableProfunctor's. Composites are themselves decidable, so searches nest.
module Proarrow.Category.Enriched.Thin.Composition where

import Data.Kind (Constraint)
import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat)
import Prelude (type (~))

import Proarrow.Category.Enriched.Matrix (Length, MatMul, Pro)
import Proarrow.Category.Enriched.Thin
  ( Decidable
  , DecidableProfunctor (..)
  , Decision (..)
  , Enumerable (..)
  , Member (..)
  , ObjList (..)
  , Thin
  , ThinProfunctor (..)
  , mapDecision
  )
import Proarrow.Category.Instance.Bool (BOOL (..))
import Proarrow.Colimit.BinaryCoproduct (type (||))
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), lmap, rmap, type (+->))
import Proarrow.Functor (FunctorForRep (..), withMappedOb)
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..), withObCorep)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), RepCostar (..), Representable (..), withObRep)

-- | How a composite @p ':.:' q@ of thin profunctors decides its arrows. In general
-- @'HasArrow' (p :.: q) a c@ is an /existential/ over the objects @b@ of the middle category
-- (the join @⋁_b p(a,b) ∧ q(b,c)@ in the enriching @Bool@), which a 'Constraint' cannot express.
-- But when the left leg is corepresented (@f a ≤ b@, a companion) or the right leg represented
-- (@b ≤ g c@, a conjoint) the middle object is determined and the existential collapses to a
-- substitution: @q (f a) c@, respectively @p a (g c)@. The strategy is chosen by the closed
-- family 'ThinCompStrategy' from the shape of the legs, so that the one 'ThinProfunctor'
-- instance for ':.:' never overlaps with anything; a composite of two non-representable legs
-- falls back to 'BySearch', which enumerates the middle category and decides both legs at each
-- object ('Search'). ('Proarrow.Profunctor.Instance.Star.Star' and
-- 'Proarrow.Profunctor.Instance.Costar.Costar' have the same two shapes, but functors between thin
-- kinds are written as 'FunctorForRep's here, so 'Rep'\/'Corep' cover them.)
type data ThinComp = ByLeft | ByRight | BySearch

type ThinCompStrategy :: forall {i} {j} {k}. (j +-> k) -> (i +-> j) -> ThinComp
type family ThinCompStrategy p q where
  ThinCompStrategy (RepCostar p) q = ByLeft
  ThinCompStrategy (Corep f) q = ByLeft
  ThinCompStrategy p (Rep g) = ByRight
  ThinCompStrategy p (CorepStar q) = ByRight
  ThinCompStrategy p q = BySearch

type ComposeThin :: forall {i} {j} {k}. ThinComp -> (j +-> k) -> (i +-> j) -> Constraint
class (ThinProfunctor p, ThinProfunctor q) => ComposeThin s (p :: j +-> k) (q :: i +-> j) where
  type HasArrowComp s p q (a :: k) (c :: i) :: Constraint
  arrComp :: (Ob (a :: k), Ob (c :: i), HasArrowComp s p q a c) => (p :.: q) a c
  withArrComp :: (p :.: q) a c -> ((HasArrowComp s p q a c, Ob a, Ob c) => r) -> r

-- | A corepresented left leg forces the middle object down to @p % a@.
instance (Representable p, Thin j, ThinProfunctor q) => ComposeThin ByLeft (RepCostar p :: j +-> k) (q :: i +-> j) where
  type HasArrowComp ByLeft (RepCostar p) q a c = HasArrow q (p % a) c
  arrComp @a @c = withObRep @p @a (RepCostar id :.: arr @q @(p % a) @c)
  withArrComp (RepCostar f :.: q) r = withArr (lmap f q) r

instance (FunctorForRep f, Thin j, ThinProfunctor q) => ComposeThin ByLeft (Corep f :: j +-> k) (q :: i +-> j) where
  type HasArrowComp ByLeft (Corep f) q a c = HasArrow q (f @ a) c
  arrComp @a @c = withMappedOb @f @a (Corep id :.: arr @q @(f @ a) @c)
  withArrComp (Corep f :.: q) r = withArr (lmap f q) r

-- | A represented right leg forces the middle object up to @g @ c@.
instance (ThinProfunctor p, FunctorForRep g, Thin j) => ComposeThin ByRight (p :: j +-> k) (Rep g :: i +-> j) where
  type HasArrowComp ByRight p (Rep g) a c = HasArrow p a (g @ c)
  arrComp @a @c = withMappedOb @g @c (arr @p @a @(g @ c) :.: Rep id)
  withArrComp (p :.: Rep g) r = withArr (rmap g p) r

instance (ThinProfunctor p, Corepresentable q, Thin j) => ComposeThin ByRight (p :: j +-> k) (CorepStar q :: i +-> j) where
  type HasArrowComp ByRight p (CorepStar q) a c = HasArrow p a (q %% c)
  arrComp @a @c = withObCorep @q @c (arr @p @a @(q %% c) :.: CorepStar id)
  withArrComp (p :.: CorepStar g) r = withArr (rmap g p) r

instance (ComposeThin (ThinCompStrategy p q) p q) => ThinProfunctor (p :.: q) where
  type HasArrow (p :.: q) a c = HasArrowComp (ThinCompStrategy p q) p q a c
  arr = arrComp @(ThinCompStrategy p q)
  withArr = withArrComp @(ThinCompStrategy p q)

-- | The arrows of a composite by search: is there an object @b@ among @bs@ with both @p a b@ and
-- @q b c@? Over the full object list this is the join @⋁_b p(a,b) ∧ q(b,c)@: matrix multiplication
-- ('MatMul') in the enriching 'BOOL', the type-level twin of "Proarrow.Category.Instance.FinRel".
type Search :: forall {i} {j} {k}. [j] -> (j +-> k) -> (i +-> j) -> k -> i -> BOOL
type Search bs p q a c = MatMul BOOL bs (Pro p) (Pro q) a c

-- | Neither leg representable: search the middle category for an object that both legs accept.
instance
  (DecidableProfunctor p, DecidableProfunctor q, Enumerable j)
  => ComposeThin BySearch (p :: j +-> k) (q :: i +-> j)
  where
  type HasArrowComp BySearch (p :: j +-> k) q a c = Search (Objects j) p q a c ~ TRU
  arrComp @a @c = case search @p @q @a @c (objects @j) of Yes x -> x
  withArrComp (p :.: q) r = found p q r

-- | Walk the object list deciding both legs at each object; a hit is the composite, and a miss
-- reduces the search to the tail of the list.
search
  :: forall {i} {j} {k} (p :: j +-> k) (q :: i +-> j) (a :: k) (c :: i) (bs :: [j])
   . (DecidableProfunctor p, DecidableProfunctor q, Ob a, Ob c)
  => ObjList bs -> Decision (p :.: q) a c (Search bs p q a c)
search ONil = No
search (OCons @b bs) = case (decide @p @a @b, decide @q @b @c) of
  (Yes x, Yes y) -> Yes (x :.: y)
  (No, _) -> search @p @q @a @c bs
  (Yes _, No) -> search @p @q @a @c bs

-- | An actual composite proves the search succeeds: locate its middle object in the list, then at
-- that position both legs hold and the disjunction is 'TRU' whatever the rest of the list says.
found
  :: forall {i} {j} {k} (p :: j +-> k) (q :: i +-> j) (a :: k) (b :: j) (c :: i) r
   . (DecidableProfunctor p, DecidableProfunctor q, Enumerable j)
  => p a b -> q b c -> ((Search (Objects j) p q a c ~ TRU, Ob a, Ob c) => r) -> r
found p q r = toHolds p (toHolds q (go (member @j @b) r))
  where
    go
      :: forall bs
       . (Holds p a b ~ TRU, Holds q b c ~ TRU)
      => Member b bs -> ((Search bs p q a c ~ TRU) => r) -> r
    go Here r' = r'
    go (There m) r' = go m r'

-- | Whether a composite decides its arrows, by the same strategy as 'ComposeThin': a representable
-- leg is substituted away and the other leg decided, a search is decided by running it. This is
-- what makes composites decidable in turn, so that searches can nest.
type DecideComp :: forall {i} {j} {k}. ThinComp -> (j +-> k) -> (i +-> j) -> Constraint
class (ComposeThin s p q) => DecideComp s (p :: j +-> k) (q :: i +-> j) where
  type HoldsComp s p q (a :: k) (c :: i) :: BOOL
  decideComp :: (Ob (a :: k), Ob (c :: i)) => Decision (p :.: q) a c (HoldsComp s p q a c)
  toHoldsComp :: (p :.: q) a c -> ((HoldsComp s p q a c ~ TRU, Ob a, Ob c) => r) -> r

instance
  (Representable p, Thin j, DecidableProfunctor q)
  => DecideComp ByLeft (RepCostar p :: j +-> k) (q :: i +-> j)
  where
  type HoldsComp ByLeft (RepCostar p) q a c = Holds q (p % a) c
  decideComp @a @c = withObRep @p @a (mapDecision (RepCostar id :.:) (decide @q @(p % a) @c))
  toHoldsComp (RepCostar f :.: q) r = toHolds (lmap f q) r

instance
  (FunctorForRep f, Thin j, DecidableProfunctor q)
  => DecideComp ByLeft (Corep f :: j +-> k) (q :: i +-> j)
  where
  type HoldsComp ByLeft (Corep f) q a c = Holds q (f @ a) c
  decideComp @a @c = withMappedOb @f @a (mapDecision (Corep id :.:) (decide @q @(f @ a) @c))
  toHoldsComp (Corep f :.: q) r = toHolds (lmap f q) r

instance
  (DecidableProfunctor p, FunctorForRep g, Thin j)
  => DecideComp ByRight (p :: j +-> k) (Rep g :: i +-> j)
  where
  type HoldsComp ByRight p (Rep g) a c = Holds p a (g @ c)
  decideComp @a @c = withMappedOb @g @c (mapDecision (:.: Rep id) (decide @p @a @(g @ c)))
  toHoldsComp (p :.: Rep g) r = toHolds (rmap g p) r

instance
  (DecidableProfunctor p, Corepresentable q, Thin j)
  => DecideComp ByRight (p :: j +-> k) (CorepStar q :: i +-> j)
  where
  type HoldsComp ByRight p (CorepStar q) a c = Holds p a (q %% c)
  decideComp @a @c = withObCorep @q @c (mapDecision (:.: CorepStar id) (decide @p @a @(q %% c)))
  toHoldsComp (p :.: CorepStar g) r = toHolds (rmap g p) r

instance
  (DecidableProfunctor p, DecidableProfunctor q, Enumerable j)
  => DecideComp BySearch (p :: j +-> k) (q :: i +-> j)
  where
  type HoldsComp BySearch (p :: j +-> k) q a c = Search (Objects j) p q a c
  decideComp @a @c = search @p @q @a @c (objects @j)
  toHoldsComp = withArrComp @BySearch

instance (DecideComp (ThinCompStrategy p q) p q) => DecidableProfunctor (p :.: q) where
  type Holds (p :.: q) a c = HoldsComp (ThinCompStrategy p q) p q a c
  decide @a @c = decideComp @(ThinCompStrategy p q) @p @q @a @c
  toHolds = toHoldsComp @(ThinCompStrategy p q)

-- * Reachability: the closure of a decidable graph

-- | A walk of at most @n@ steps along @p@, finished by an arrow of the base category. The truth of
-- @'Walk' n p a b@ is the iterated search 'WalkHolds', the value-level twin of the type-level
-- 'Proarrow.Category.Enriched.Matrix.Walks', and 'decide' produces the path.
type Walk :: forall {k}. Nat -> (k +-> k) -> k +-> k
data Walk n p a b where
  Done :: (a ~> b) -> Walk n p a b
  Step :: p a b -> Walk n p b c -> Walk ('S n) p a c

instance (Profunctor p) => Profunctor (Walk n p) where
  dimap l r (Done f) = Done (r . f . l)
  dimap l r (Step e w) = Step (lmap l e) (rmap r w)
  r \\ Done f = r \\ f
  r \\ Step e w = r \\ e \\ w

-- | An arrow of the base, or an edge followed by a shorter walk: one more matrix multiplication.
type WalkHolds :: forall {k}. Nat -> (k +-> k) -> k -> k -> BOOL
type family WalkHolds n p a b where
  WalkHolds 'Z (p :: k +-> k) a b = Holds (Hom k) a b
  WalkHolds ('S n) (p :: k +-> k) a b = Holds (Hom k) a b || Search (Objects k) p (Walk n p) a b

instance (SNatI n, DecidableProfunctor p, Decidable k, Enumerable k) => ThinProfunctor (Walk n (p :: k +-> k))

instance (SNatI n, DecidableProfunctor p, Decidable k, Enumerable k) => DecidableProfunctor (Walk n (p :: k +-> k)) where
  type Holds (Walk n (p :: k +-> k)) a b = WalkHolds n p a b
  decide @a @b = case snat @n of
    SZ -> mapDecision Done (decide @(Hom k) @a @b)
    SS @m -> case decide @(Hom k) @a @b of
      Yes f -> Yes (Done f)
      No -> mapDecision (\(e :.: w) -> Step e w) (search @p @(Walk m p) @a @b (objects @k))
  toHolds w r = case snat @n of
    SZ -> case w of Done f -> toHolds f r
    SS -> case w of
      Done f -> toHolds f r
      Step e w' -> found e w' r

-- | Reachability along @p@: a walk of at most as many steps as there are objects, which is all of
-- reachability, since a shortest walk never revisits an object. The reflexive-transitive closure of
-- a decidable relation, with the path as witness.
type Reachable (p :: k +-> k) = Walk (Length (Objects k)) p
