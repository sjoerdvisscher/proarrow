{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Composition of thin profunctors. In general the arrows of a composite @p ':.:' q@ are an
-- existential over the objects of the middle category, which a 'Constraint' cannot express. This
-- module dispatches on the shape of the legs, so that the single 'ThinProfunctor' instance for
-- ':.:' never overlaps with anything: a representable leg pins the middle object down, and
-- otherwise the middle category is searched ('Search'), which needs it to be 'Enumerable' and both
-- legs to be 'DecidableProfunctor's. Composites are themselves decidable, so searches nest.
module Proarrow.Category.Enriched.Thin.Composition where

import Data.Kind (Constraint, Type)
import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat)
import Prelude (type (~))

import Proarrow.Category.Enriched (Enriched, EnrichedProfunctor (..), HomObj)
import Proarrow.Category.Enriched.Quantale (MinIs (..), Quantale (..), checkedArrow, splitUnit)
import Proarrow.Category.Enriched.Thin
  ( Decidable
  , DecidableProfunctor (..)
  , Decision (..)
  , Enumerable (..)
  , Finite (..)
  , IndexedList (..)
  , Length
  , Member (..)
  , Thin
  , ThinProfunctor (..)
  , mapDecision
  , member
  )
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Cost (COST)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Hom, Kind, Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Core qualified as P
import Proarrow.Functor (FunctorForRep (..), withMappedOb)
import Proarrow.Object (pattern Objs)
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
  withArrComp (RepCostar f :.: q) r = withArr (P.lmap f q) r

instance (FunctorForRep f, Thin j, ThinProfunctor q) => ComposeThin ByLeft (Corep f :: j +-> k) (q :: i +-> j) where
  type HasArrowComp ByLeft (Corep f) q a c = HasArrow q (f @ a) c
  arrComp @a @c = withMappedOb @f @a (Corep id :.: arr @q @(f @ a) @c)
  withArrComp (Corep f :.: q) r = withArr (P.lmap f q) r

-- | A represented right leg forces the middle object up to @g @ c@.
instance (ThinProfunctor p, FunctorForRep g, Thin j) => ComposeThin ByRight (p :: j +-> k) (Rep g :: i +-> j) where
  type HasArrowComp ByRight p (Rep g) a c = HasArrow p a (g @ c)
  arrComp @a @c = withMappedOb @g @c (arr @p @a @(g @ c) :.: Rep id)
  withArrComp (p :.: Rep g) r = withArr (P.rmap g p) r

instance (ThinProfunctor p, Corepresentable q, Thin j) => ComposeThin ByRight (p :: j +-> k) (CorepStar q :: i +-> j) where
  type HasArrowComp ByRight p (CorepStar q) a c = HasArrow p a (q %% c)
  arrComp @a @c = withObCorep @q @c (arr @p @a @(q %% c) :.: CorepStar id)
  withArrComp (p :.: CorepStar g) r = withArr (P.rmap g p) r

instance (ComposeThin (ThinCompStrategy p q) p q) => ThinProfunctor (p :.: q) where
  type HasArrow (p :.: q) a c = HasArrowComp (ThinCompStrategy p q) p q a c
  arr = arrComp @(ThinCompStrategy p q)
  withArr = withArrComp @(ThinCompStrategy p q)

-- | The join @⋁_b p(a,b) ⊗ w_b@ of an edge out of @a@ with whatever the vector holds for where
-- that edge lands: one row of the matrix of @p@ against a vector, over the given middle objects.
-- The objects and the vector are walked in step, so @ws@ is always the vector cut down to @bs@.
--
-- This is the module's one join. Composing two profunctors multiplies by a column read off the
-- right-hand one ('MatMul'); the closure multiplies by the previous iterate ('Walks'), which is
-- what lets that iterate be computed once instead of once per pair.
type MatVec :: forall {j} {k}. forall (v :: Kind) -> [j] -> [v] -> (j +-> k) -> k -> v
type family MatVec v bs ws p a where
  MatVec v '[] ws p a = InitialObject
  MatVec v (b ': bs) (w ': ws) p a = (ProObj v p a b ** w) || MatVec v bs ws p a

-- | One column of the matrix of an enriched profunctor: its hom-objects into @c@, over the given
-- objects.
type MatCol :: forall {i} {j}. forall (v :: Kind) -> [j] -> (i +-> j) -> i -> [v]
type family MatCol v bs q c where
  MatCol v '[] q c = '[]
  MatCol v (b ': bs) q c = ProObj v q b c ': MatCol v bs q c

-- | Matrix multiplication over a list of middle objects, @⋁_b p(a,b) ⊗ q(b,c)@: the hom-object of
-- the composite of two enriched profunctors when the middle category is enumerable. The type-level
-- twin of "Proarrow.Category.Instance.FinRel".
type MatMul :: forall {i} {j} {k}. forall (v :: Kind) -> [j] -> (j +-> k) -> (i +-> j) -> k -> i -> v
type MatMul v bs p q a c = MatVec v bs (MatCol v bs q c) p a

-- | The arrows of a composite by search: is there an object @b@ among @bs@ with both @p a b@ and
-- @q b c@? Over the full object list this is the join @⋁_b p(a,b) ∧ q(b,c)@, which is 'MatMul' in
-- the enriching 'BOOL'.
type Search :: forall {i} {j} {k}. [j] -> (j +-> k) -> (i +-> j) -> k -> i -> BOOL
type Search bs p q a c = MatMul BOOL bs p q a c

-- | Neither leg representable: search the middle category for an object that both legs accept.
instance
  (DecidableProfunctor p, DecidableProfunctor q, Enumerable j)
  => ComposeThin BySearch (p :: j +-> k) (q :: i +-> j)
  where
  type HasArrowComp BySearch (p :: j +-> k) q a c = Search (Objects j) p q a c ~ TRU
  arrComp @a @c = case search @p @q @a @c (finite @j) of Yes x -> x
  withArrComp (p :.: q) r = found p q r

-- | Walk the object list deciding both legs at each object; a hit is the composite, and a miss
-- reduces the search to the tail of the list.
search
  :: forall {i} {j} {k} (p :: j +-> k) (q :: i +-> j) (a :: k) (c :: i) (bs :: [j])
   . (DecidableProfunctor p, DecidableProfunctor q, Enumerable j, Ob a, Ob c)
  => IndexedList bs -> Decision (p :.: q) a c (Search bs p q a c)
search FNil = No
search (FCons @b bs) = withOb @j @b case (decide @p @a @b, decide @q @b @c) of
  (Yes x, Yes y) -> Yes (x :.: y)
  (No, _) -> search @p @q @a @c bs
  (Yes _, No) -> search @p @q @a @c bs

-- | An actual composite proves the search succeeds: locate its middle object in the list, then at
-- that position both legs hold and the disjunction is 'TRU' whatever the rest of the list says.
found
  :: forall {i} {j} {k} (p :: j +-> k) (q :: i +-> j) (a :: k) (b :: j) (c :: i) r
   . (DecidableProfunctor p, DecidableProfunctor q, Enumerable j)
  => p a b -> q b c -> ((Search (Objects j) p q a c ~ TRU, Ob a, Ob c) => r) -> r
found p q r = toHolds p (toHolds q (go (member @b) r))
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
  toHoldsComp (RepCostar f :.: q) r = toHolds (P.lmap f q) r

instance
  (FunctorForRep f, Thin j, DecidableProfunctor q)
  => DecideComp ByLeft (Corep f :: j +-> k) (q :: i +-> j)
  where
  type HoldsComp ByLeft (Corep f) q a c = Holds q (f @ a) c
  decideComp @a @c = withMappedOb @f @a (mapDecision (Corep id :.:) (decide @q @(f @ a) @c))
  toHoldsComp (Corep f :.: q) r = toHolds (P.lmap f q) r

instance
  (DecidableProfunctor p, FunctorForRep g, Thin j)
  => DecideComp ByRight (p :: j +-> k) (Rep g :: i +-> j)
  where
  type HoldsComp ByRight p (Rep g) a c = Holds p a (g @ c)
  decideComp @a @c = withMappedOb @g @c (mapDecision (:.: Rep id) (decide @p @a @(g @ c)))
  toHoldsComp (p :.: Rep g) r = toHolds (P.rmap g p) r

instance
  (DecidableProfunctor p, Corepresentable q, Thin j)
  => DecideComp ByRight (p :: j +-> k) (CorepStar q :: i +-> j)
  where
  type HoldsComp ByRight p (CorepStar q) a c = Holds p a (q %% c)
  decideComp @a @c = withObCorep @q @c (mapDecision (:.: CorepStar id) (decide @p @a @(q %% c)))
  toHoldsComp (p :.: CorepStar g) r = toHolds (P.rmap g p) r

instance
  (DecidableProfunctor p, DecidableProfunctor q, Enumerable j)
  => DecideComp BySearch (p :: j +-> k) (q :: i +-> j)
  where
  type HoldsComp BySearch (p :: j +-> k) q a c = Search (Objects j) p q a c
  decideComp @a @c = search @p @q @a @c (finite @j)
  toHoldsComp = withArrComp @BySearch

instance (DecideComp (ThinCompStrategy p q) p q) => DecidableProfunctor (p :.: q) where
  type Holds (p :.: q) a c = HoldsComp (ThinCompStrategy p q) p q a c
  decide @a @c = decideComp @(ThinCompStrategy p q) @p @q @a @c
  toHolds = toHoldsComp @(ThinCompStrategy p q)

-- * Closure: walks along a graph, in any enriching category

-- | A walk of at most @n@ steps along @p@, finished by an arrow of the base category. Its
-- hom-object in any enriching category is 'Walks': at 'BOOL' the truth of the walk, decided with
-- the path as witness; at 'COST' the shortest distance.
type Walk :: forall {k}. Nat -> (k +-> k) -> k +-> k
data Walk n p a b where
  Done :: forall {k} n (p :: k +-> k) a b. (a ~> b) -> Walk n p a b
  Step :: forall {k} n (p :: k +-> k) a c b. p a c -> Walk n p c b -> Walk ('S n) p a b

instance (Profunctor p) => Profunctor (Walk n p) where
  dimap l r (Done f) = Done (r . f . l)
  dimap l r (Step e w) = Step (P.lmap l e) (P.rmap r w)
  r \\ Done f = r \\ f
  r \\ Step e w = r \\ e \\ w

-- | The hom-object of a walk of at most @n@ steps, in any enriching category @v@: an arrow of the
-- base, or an edge followed by one entry of the previous iterate ('WalkRow'). Naming the whole
-- iterate rather than a shorter walk per pair is what keeps this affordable. At 'BOOL' it is the
-- truth of 'Walk', at 'COST' the shortest distance, computed by GHC at the type level and by 'row'
-- at the value level.
type Walks :: forall {k}. forall (v :: Kind) -> Nat -> (k +-> k) -> k -> k -> v
type family Walks v n p a b where
  Walks v 'Z (p :: k +-> k) a b = HomObj v a b
  Walks v ('S n) (p :: k +-> k) a b = HomObj v a b || MatVec v (Objects k) (WalkRow v n p b) p a

-- | The @n@-th iterate of the fixed point for a fixed target @b@: the hom-object of the walks of at
-- most @n@ steps into @b@, one entry per object, in the order of 'Objects'. It starts as the column
-- of the base hom-objects, there being no step to take yet, and grows by 'NextRow'.
--
-- Each iterate is written in terms of the whole previous one, so it is computed once and read by
-- every object. That sharing is what makes the fixed point affordable: the work is the number of
-- steps times the square of the number of objects, where a recursion per pair of objects would
-- instead cost the number of objects to the power of the number of steps.
type WalkRow :: forall {k}. forall (v :: Kind) -> Nat -> (k +-> k) -> k -> [v]
type family WalkRow v n p b where
  WalkRow v 'Z (p :: k +-> k) b = MatCol v (Objects k) (Hom k) b
  WalkRow v ('S n) (p :: k +-> k) b = NextRow v (Objects k) (WalkRow v n p b) p b

-- | One more step, taken for every object at once: an arrow of the base, or an edge into the
-- previous iterate ('MatVec').
type NextRow :: forall {k}. forall (v :: Kind) -> [k] -> [v] -> (k +-> k) -> k -> [v]
type family NextRow v as row p b where
  NextRow v '[] row p b = '[]
  NextRow v (a ': as) row (p :: k +-> k) b =
    (HomObj v a b || MatVec v (Objects k) row p a) ': NextRow v as row p b

-- | The Kleene closure of @p@: walks of at most as many steps as there are objects, which is all
-- of them, since a shortest walk never revisits an object. It is the free category on the graph
-- @p@ in whatever @p@ is enriched in: at 'BOOL' the reflexive-transitive closure of a relation, with
-- the path as witness ('decide'); at 'COST' the free Lawvere metric space, with the shortest
-- distances ('withProObj') and the shortest paths ('shortest').
type Closure (p :: k +-> k) = Walk (Length (Objects k)) p

-- * Graded walks

-- | What the closure needs of its ingredients: a quantale to compute in, an enriched graph over an
-- enumerable enriched base, and a known number of steps.
type Closing :: forall {k}. Kind -> Nat -> (k +-> k) -> Constraint
type Closing v n (p :: k +-> k) = (SNatI n, Quantale v, EnrichedProfunctor v p, Enriched v k, Enumerable k)

-- | A walk graded by its cost: each piece comes with a budget, an arrow of @v@ into the piece's
-- hom-object, and the grade of the walk is the tensor of the budgets. A walk at grade @d@ is a
-- generalised element of the closure, @d ~> 'Walks' v n p a b@ ('underlyingAt'), and 'shortest'
-- produces one at grade exactly the hom-object.
type GradedWalk :: forall {k}. forall (v :: Kind) -> Nat -> (k +-> k) -> v -> k -> k -> Type
data GradedWalk v n p d a b where
  DoneAt :: forall {k} v n (p :: k +-> k) d a b. (Ob a, Ob b) => (d ~> HomObj v a b) -> GradedWalk v n p d a b
  StepAt
    :: forall {k} v n (p :: k +-> k) a c b e d
     . (Ob a, Ob b, Ob c, Ob e, Ob d)
    => (e ~> ProObj v p a c) -> GradedWalk v n p d c b -> GradedWalk v ('S n) p (e ** d) a b

-- | The @n@-th iterate reflected to the value level: every object paired with its own entry, which
-- is exactly the hom-object of the walks from it. 'row' builds one and everything that needs a
-- shorter walk reads it, so the value level shares its work the same way the type level does.
type Row :: forall {k}. forall (v :: Kind) -> Nat -> (k +-> k) -> k -> [k] -> [v] -> Type
data Row v n p b as ws where
  RNil :: Row v n p b '[] '[]
  RCons
    :: forall {k} a as v ws n (p :: k +-> k) b
     . (Ob a, Ob (Walks v n p a b))
    => Row v n p b as ws -> Row v n p b (a ': as) (Walks v n p a b ': ws)

-- | The @n@-th iterate: the base hom-objects, then one more step for every object at a time.
row :: forall {k} v n (p :: k +-> k) b. (Closing v n p, Ob b) => Row v n p b (Objects k) (WalkRow v n p b)
row = case snat @n of
  SZ ->
    let homRow :: forall as. IndexedList as -> Row v 'Z p b as (MatCol v as (Hom k) b)
        homRow FNil = RNil
        homRow (FCons @a as) = withOb @k @a (withProObj @v @(Hom k) @a @b (RCons (homRow as)))
    in homRow (finite @k)
  SS @n' ->
    let prev = row @v @n' @p @b
        nextRow :: forall as. IndexedList as -> Row v ('S n') p b as (NextRow v as (WalkRow v n' p b) p b)
        nextRow FNil = RNil
        nextRow (FCons @a as) =
          withOb @k @a
            ( withProObj @v @(Hom k) @a @b
                ( withObMatVec @a
                    prev
                    ( withObCoprod @v @(HomObj v a b) @(MatVec v (Objects k) (WalkRow v n' p b) p a)
                        (RCons (nextRow as))
                    )
                )
            )
    in nextRow (finite @k)

-- | Object evidence for the hom-object of a walk: read the object's own entry out of an iterate.
withObRow
  :: forall {k} (a :: k) v n (p :: k +-> k) b cs ws r
   . Member a cs -> Row v n p b cs ws -> ((Ob (Walks v n p a b)) => r) -> r
withObRow Here (RCons _) r = r
withObRow (There m) (RCons rest) r = withObRow m rest r

-- | The same, for a caller that is not already holding the iterate.
withObWalks
  :: forall {k} v n (p :: k +-> k) a b r
   . (Closing v n p, Ob a, Ob b)
  => ((Ob (Walks v n p a b)) => r) -> r
withObWalks = withObRow (member @a) (row @v @n @p @b)

-- | Object evidence for one summand of 'MatVec': an edge and its tensor with the entry after it.
withObStep
  :: forall {k} v n (p :: k +-> k) a c b r
   . (Closing v n p, Ob a, Ob c, Ob (Walks v n p c b))
  => ((Ob (ProObj v p a c), Ob (ProObj v p a c ** Walks v n p c b)) => r) -> r
withObStep r = withProObj @v @p @a @c (withOb2 @v @(ProObj v p a c) @(Walks v n p c b) r)

-- | Object evidence for the join over the given middle objects.
withObMatVec
  :: forall {k} a v n (p :: k +-> k) b cs ws r
   . (Closing v n p, Ob a)
  => Row v n p b cs ws -> ((Ob (MatVec v cs ws p a)) => r) -> r
withObMatVec RNil r = r
withObMatVec (RCons @c @cs' @_ @ws' rest) r =
  withObStep @v @n @p @a @c @b
    ( withObMatVec @a
        rest
        (withObCoprod @v @(ProObj v p a c ** Walks v n p c b) @(MatVec v cs' ws' p a) r)
    )

-- | A graded walk is a generalised element of the closure: inject it into the join at its middle
-- object.
underlyingAt
  :: forall {k} v n (p :: k +-> k) d a b
   . (Closing v n p)
  => GradedWalk v n p d a b -> d ~> Walks v n p a b
underlyingAt (DoneAt g) = case snat @n of
  SZ -> g
  SS @n' ->
    withProObj @v @(Hom k) @a @b
      ( withObMatVec @a
          (row @v @n' @p @b)
          (lft @v @(HomObj v a b) @(MatVec v (Objects k) (WalkRow v n' p b) p a))
      )
      . g
underlyingAt (StepAt @_ @_ @_ @_ @c ee w) = case snat @n of
  SS @n' -> stepAt @v @n' @p @a @c @b ee (underlyingAt w)

-- | An edge with a budget, followed by a generalised element of the shorter walks.
stepAt
  :: forall {k} v n (p :: k +-> k) a c b e d
   . (Closing v n p, Ob a, Ob b, Ob c)
  => (e ~> ProObj v p a c) -> (d ~> Walks v n p c b) -> (e ** d) ~> Walks v ('S n) p a b
stepAt ee uw = case ee ** uw of
  step@Objs ->
    let rw = row @v @n @p @b
    in withProObj @v @(Hom k) @a @b
         ( withObMatVec @a
             rw
             ( withObRow
                 (member @c)
                 rw
                 ( rgt @v @(HomObj v a b) @(MatVec v (Objects k) (WalkRow v n p b) p a)
                     . inject @a rw (member @c)
                     . step
                 )
             )
         )

-- | The injection of one summand into the join over the middle objects.
inject
  :: forall {k} a v n (p :: k +-> k) b c cs ws
   . (Closing v n p, Ob a, Ob c, Ob (Walks v n p c b))
  => Row v n p b cs ws -> Member c cs -> (ProObj v p a c ** Walks v n p c b) ~> MatVec v cs ws p a
inject RNil m = case m of {}
inject (RCons @_ @cs' @_ @ws' rest) Here =
  withObStep @v @n @p @a @c @b
    ( withObMatVec @a
        rest
        (lft @v @(ProObj v p a c ** Walks v n p c b) @(MatVec v cs' ws' p a))
    )
inject (RCons @c' @cs' @_ @ws' rest) (There m) =
  withObStep @v @n @p @a @c' @b
    ( withObMatVec @a
        rest
        ( rgt @v @(ProObj v p a c' ** Walks v n p c' b) @(MatVec v cs' ws' p a)
            . inject @a rest m
        )
    )

-- | A walk of pieces at the unit, as a generalised element at the unit.
underlyingWalk
  :: forall {k} v n (p :: k +-> k) a b
   . (Closing v n p)
  => Walk n p a b -> Unit ~> Walks v n p a b
underlyingWalk (Done f@Objs) = underlyingAt @v @n @p @Unit @a @b (DoneAt @v @n @p @Unit @a @b (underlying @v @(Hom k) @a @b f))
underlyingWalk (Step @_ @_ @_ @c e@Objs w@Objs) = case snat @n of
  SS @n' -> stepAt @v @n' @p @a @c @b (underlying @v @p e) (underlyingWalk @v w) . leftUnitorInv @v @Unit

-- | The best walk between two points, graded by exactly their hom-object: a shortest path at
-- 'COST', a path or the absence of one at 'BOOL'. At every join it keeps the summand the join is
-- ('minIs'); a pair no walk connects gets the empty walk at 'InitialObject'.
shortest
  :: forall {k} v n (p :: k +-> k) a b
   . (Closing v n p, Ob a, Ob b)
  => GradedWalk v n p (Walks v n p a b) a b
shortest = case snat @n of
  SZ -> withProObj @v @(Hom k) @a @b (DoneAt @v @n @p (obj @(HomObj v a b)))
  SS @n' ->
    let rw = row @v @n' @p @b
    in withProObj @v @(Hom k) @a @b
         ( withObMatVec @a rw case minIs @v @(HomObj v a b) @(MatVec v (Objects k) (WalkRow v n' p b) p a) of
             MinLeft -> DoneAt @v @n @p (obj @(HomObj v a b))
             MinRight -> best @a rw
         )

-- | The best walk through one of the given middle objects.
best
  :: forall {k} a v n (p :: k +-> k) b cs ws
   . (Closing v n p, Ob a, Ob b)
  => Row v n p b cs ws -> GradedWalk v ('S n) p (MatVec v cs ws p a) a b
best RNil = withProObj @v @(Hom k) @a @b (DoneAt @v @('S n) @p (initiate @v @(HomObj v a b)))
best (RCons @c @cs' @_ @ws' rest) =
  withObStep @v @n @p @a @c @b
    ( withObMatVec @a rest case minIs @v @(ProObj v p a c ** Walks v n p c b) @(MatVec v cs' ws' p a) of
        MinLeft -> StepAt (obj @(ProObj v p a c)) (shortest @v @n @p @c @b)
        MinRight -> best @a rest
    )

-- | A graded walk together with a unit into its grade is a walk of pieces at the unit: the budget
-- splits over the pieces ('splitUnit') and each piece is read off with 'enriched'.
walkAt
  :: forall {k} v n (p :: k +-> k) d a b
   . (Closing v n p)
  => (Unit ~> d) -> GradedWalk v n p d a b -> Walk n p a b
walkAt ud (DoneAt g) = Done (enriched @v @(Hom k) @a @b (g . ud))
walkAt ud (StepAt @_ @_ @_ @_ @c @_ @e @d' ee w) = case snat @n of
  SS -> case splitUnit @e @d' ud of
    (ue, ud') -> Step (enriched @v @p @a @c (ee . ue)) (walkAt @v ud' w)

-- * Reachability and shortest paths

instance (SNatI n, DecidableProfunctor p, Decidable k, Enumerable k) => ThinProfunctor (Walk n (p :: k +-> k))

-- | Reachability: the truth of a walk is its hom-object in 'BOOL', and 'shortest' at grade 'TRU' is
-- the path.
instance (SNatI n, DecidableProfunctor p, Decidable k, Enumerable k) => DecidableProfunctor (Walk n (p :: k +-> k)) where
  type Holds (Walk n (p :: k +-> k)) a b = Walks BOOL n p a b
  decide @a @b = withObWalks @BOOL @n @p @a @b case obj @(Walks BOOL n p a b) of
    Tru -> Yes (walkAt @BOOL Tru (shortest @BOOL @n @p @a @b))
    Fls -> No
  toHolds w@Objs r = case underlyingWalk @BOOL w of Tru -> r

-- | The action of the base on a closure: the triangle inequality. It holds for the best walks but
-- is not derived structurally, so it is a 'checkedArrow'.
checkedWalk
  :: forall {k} v n (p :: k +-> k) (x :: k) y a b c d
   . (Closing v n p, Ob x, Ob y, Ob a, Ob b, Ob c, Ob d)
  => (HomObj v x y ** Walks v n p a b) ~> Walks v n p c d
checkedWalk =
  withProObj @v @(Hom k) @x @y
    ( withObWalks @v @n @p @a @b
        ( withObWalks @v @n @p @c @d
            ( withOb2 @v @(HomObj v x y) @(Walks v n p a b)
                (checkedArrow @v @(HomObj v x y ** Walks v n p a b) @(Walks v n p c d))
            )
        )
    )

-- | Walks along a 'COST'-weighted graph form the free Lawvere metric space on it: 'withProObj' runs
-- the fixed point that computes the shortest distances, 'underlying' and 'enriched' relate a walk of
-- zero-cost pieces to a zero distance, and the actions of the base are the triangle inequality.
instance
  (SNatI n, EnrichedProfunctor COST p, Enriched COST k, Enumerable k)
  => EnrichedProfunctor COST (Walk n (p :: k +-> k))
  where
  type ProObj COST (Walk n p) a b = Walks COST n p a b
  withProObj @a @b = withObWalks @COST @n @p @a @b
  underlying = underlyingWalk @COST
  enriched @a @b f = walkAt @COST f (shortest @COST @n @p @a @b)
  rmap @a @b @c = checkedWalk @COST @n @p @b @c @a @b @a @c
  lmap @a @b @c = checkedWalk @COST @n @p @c @a @a @b @c @b
