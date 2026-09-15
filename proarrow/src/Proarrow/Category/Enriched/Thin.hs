{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Thin categories, where any two parallel arrows are equal: a 'ThinProfunctor' has at most one
-- element between any two objects, mere existence being captured by the constraint
-- @'HasArrow' p a b@. Also defines the codiscrete (always exactly one arrow) and discrete (only
-- identity arrows) special cases; 'DecidableProfunctor's, whose arrows are computed at the type
-- level as a 'BOOL' (the category thin profunctors are enriched in); and 'Indexed', 'Finite' and
-- 'Enumerable' kinds and categories, whose inhabitants are numbered, listed, and reflected to the
-- value level.
module Proarrow.Category.Enriched.Thin where

import Data.Kind (Constraint, Type)
import Data.Type.Equality (type (:~:) (..))
import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat)
import Prelude (Maybe (..), type (~))

import Proarrow.Category.Instance.Bool (BOOL (..), BoolLeq, Booleans (..), NonTrivialHolds, NonTrivialProfunctor (..))
import Proarrow.Category.Instance.Zero (Bottom (..), Zero)
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), obj, type (+->))

-- | The defaults take everything from a 'DecidableProfunctor' instance: the arrow exists when
-- @'Holds' p a b@ computes to 'TRU'.
type ThinProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => ThinProfunctor (p :: j +-> k) where
  type HasArrow (p :: j +-> k) (a :: k) (b :: j) :: Constraint
  type HasArrow p a b = Holds p a b ~ TRU
  arr :: (Ob a, Ob b, HasArrow p a b) => p a b
  default arr :: (Ob a, Ob b, DecidableProfunctor p, Holds p a b ~ TRU) => p a b
  arr = fromHolds
  withArr :: p a b -> ((HasArrow p a b, Ob a, Ob b) => r) -> r
  default withArr
    :: (DecidableProfunctor p, HasArrow p a b ~ (Holds p a b ~ TRU)) => p a b -> ((HasArrow p a b, Ob a, Ob b) => r) -> r
  withArr = toHolds

instance ThinProfunctor Zero
instance ThinProfunctor Booleans
instance (Ob ff, Ob tt) => ThinProfunctor (NonTrivialProfunctor '(ff, tt))

-- * Decidable thin profunctors

-- | The value-level shadow of a type-level 'BOOL' @h@ answering whether @p a b@ has an arrow: the
-- arrow itself when @h@ is 'TRU', nothing when it is 'FLS'.
type Decision :: forall {j} {k}. (j +-> k) -> k -> j -> BOOL -> Type
data Decision p a b h where
  Yes :: p a b -> Decision p a b TRU
  No :: Decision p a b FLS

mapDecision :: (p a b -> q c d) -> Decision p a b h -> Decision q c d h
mapDecision f (Yes x) = Yes (f x)
mapDecision _ No = No

-- | A thin profunctor whose arrows are decidable at the type level: @'Holds' p a b@ is the
-- 'BOOL'-valued profunctor a thin profunctor really is, computed by a type family, so it reduces to
-- 'TRU' or 'FLS' for concrete objects. It agrees with 'HasArrow' ('fromHolds' and 'toHolds' are the
-- two directions of that agreement, and the 'ThinProfunctor' defaults make it definitional), and
-- 'decide' computes the answer at the value level, arrow included. This is what lets a composite of
-- thin profunctors search for its middle object ("Proarrow.Category.Enriched.Thin.Composition").
type DecidableProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (ThinProfunctor p) => DecidableProfunctor (p :: j +-> k) where
  type Holds (p :: j +-> k) (a :: k) (b :: j) :: BOOL
  decide :: (Ob a, Ob b) => Decision p a b (Holds p a b)
  toHolds :: p a b -> ((Holds p a b ~ TRU, Ob a, Ob b) => r) -> r

fromHolds :: forall {j} {k} (p :: j +-> k) a b. (DecidableProfunctor p, Ob a, Ob b, Holds p a b ~ TRU) => p a b
fromHolds = case decide @p @a @b of Yes x -> x

-- | An arrow is a proof that the profunctor holds. Against a given that it does not, the proof has
-- no constructor, so @case 'holds' x of {}@ refutes an arrow of a profunctor that decides against it.
holds :: forall {j} {k} (p :: j +-> k) a b. (DecidableProfunctor p) => p a b -> Holds p a b :~: TRU
holds x = toHolds x Refl

-- | A thin category whose order is decidable at the type level.
class (DecidableProfunctor (Hom k), CategoryOf k) => Decidable k

instance (DecidableProfunctor (Hom k), CategoryOf k) => Decidable k

instance DecidableProfunctor Zero where
  type Holds Zero a b = FLS
  decide = no
  toHolds = \case {}

instance DecidableProfunctor Booleans where
  type Holds Booleans a b = BoolLeq a b
  decide @a @b = case (obj @a, obj @b) of
    (Fls, Fls) -> Yes Fls
    (Fls, Tru) -> Yes F2T
    (Tru, Tru) -> Yes Tru
    (Tru, Fls) -> No
  toHolds Fls r = r
  toHolds F2T r = r
  toHolds Tru r = r

instance (Ob ff, Ob tt) => DecidableProfunctor (NonTrivialProfunctor '(ff, tt)) where
  type Holds (NonTrivialProfunctor '(ff, tt)) a b = NonTrivialHolds ff tt a b
  decide @a @b = case (obj @a, obj @b) of
    (Fls, Fls) -> case obj @ff of
      Fls -> No
      Tru -> Yes FF
    (Fls, Tru) -> Yes FT
    (Tru, Tru) -> case obj @tt of
      Fls -> No
      Tru -> Yes TT
    (Tru, Fls) -> No
  toHolds FF r = r
  toHolds FT r = r
  toHolds TT r = r

class (ThinProfunctor (Hom k), CategoryOf k) => Thin k
instance (ThinProfunctor (Hom k), CategoryOf k) => Thin k

class (ThinProfunctor p, Ob a, Ob b, HasArrow p a b) => HasArrow' p a b where arr' :: p a b
instance (ThinProfunctor p, Ob a, Ob b, HasArrow p a b) => HasArrow' p a b where arr' = arr

type CodiscreteProfunctor :: forall {j} {k}. j +-> k -> Constraint
class
  (ThinProfunctor p, forall c d. (Ob c, Ob d) => HasArrow' p c d, Codiscrete j, Codiscrete k) =>
  CodiscreteProfunctor (p :: j +-> k)
  where
  anyArr :: (Ob a, Ob b) => p a b
instance
  (ThinProfunctor p, forall c d. (Ob c, Ob d) => HasArrow' p c d, Codiscrete j, Codiscrete k)
  => CodiscreteProfunctor (p :: j +-> k)
  where
  anyArr = arr'

type Codiscrete k = CodiscreteProfunctor (Hom k)

class ((c) => d, (d) => c) => c <=> d
instance ((c) => d, (d) => c) => c <=> d

class ((HasArrow p a b) => Bottom) => HasNoArrow p a b where
  arrowIsBottomProof :: (HasArrow p a b) => r
instance ((HasArrow p a b) => Bottom) => HasNoArrow p a b where
  arrowIsBottomProof = no

type DiscreteProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (ThinProfunctor p, forall a b. (Ob a, Ob b) => HasNoArrow p a b) => DiscreteProfunctor (p :: j +-> k) where
  exfalso :: p a b -> r
instance (ThinProfunctor p, forall a b. (Ob a, Ob b) => HasNoArrow p a b) => DiscreteProfunctor (p :: j +-> k) where
  exfalso @a @b p = withArr p (arrowIsBottomProof @p @a @b)

class ((HasArrow (Hom k) c d) <=> (c ~ d)) => ArrowIsId k c d where
  arrowIsIdProof :: (HasArrow (Hom k) c d) => ((c ~ d) => r) -> r
instance ((HasArrow (Hom k) c d) <=> (c ~ d)) => ArrowIsId k c d where
  arrowIsIdProof r = r

-- | Note: @Discrete k@ is not the same as @DiscreteProfunctor (Hom k)@!
class (Thin k, forall c d. (Ob c, Ob d) => ArrowIsId k c d) => Discrete k where
  withEq :: (a :: k) ~> b -> ((a ~ b) => r) -> r

instance (Thin k, forall c d. (Ob c, Ob d) => ArrowIsId k c d) => Discrete k where
  withEq @a @b f r = withArr f (arrowIsIdProof @k @a @b r)

-- * Indexed, finite and enumerable kinds

-- | A kind whose inhabitants are numbered: 'Index' gives each its position and 'At' reads it back,
-- so that two inhabitants are equal exactly when their indices are ('decideEq'). 'At' is partial, so
-- that finitely many inhabitants can be numbered by an initial segment of the naturals.
class Indexed k where
  type Index (a :: k) :: Nat
  type At k (i :: Nat) :: Maybe k

-- | The evidence that @a@ is numbered: its index, reflected, and 'At' reading it back.
class (SNatI (Index a), At k (Index a) ~ 'Just a) => KnownIndex (a :: k)

instance (SNatI (Index a), At k (Index a) ~ 'Just a) => KnownIndex (a :: k)

instance Indexed Nat where
  type Index n = n
  type At Nat i = 'Just i

-- | Equality of naturals, with evidence either way.
type NatEq :: Nat -> Nat -> BOOL
type family NatEq n m where
  NatEq 'Z 'Z = TRU
  NatEq ('S n) ('S m) = NatEq n m
  NatEq n m = FLS

natEq :: SNat n -> SNat m -> Decision (:~:) n m (NatEq n m)
natEq SZ SZ = Yes Refl
natEq (SS @n) (SS @m) = mapDecision (\Refl -> Refl) (natEq (snat @n) (snat @m))
natEq SZ SS = No
natEq SS SZ = No

natEqRefl :: SNat n -> NatEq n n :~: TRU
natEqRefl SZ = Refl
natEqRefl (SS @n) = natEqRefl (snat @n)

-- | Two numbered inhabitants are equal exactly when their indices are.
type Equal (a :: k) (b :: k) = NatEq (Index a) (Index b)

decideEq :: forall {k} (a :: k) b. (KnownIndex a, KnownIndex b) => Decision (:~:) a b (Equal a b)
decideEq = case natEq (snat @(Index a)) (snat @(Index b)) of
  Yes Refl -> Yes Refl
  No -> No

type Lookup :: [k] -> Nat -> Maybe k
type family Lookup xs i where
  Lookup '[] i = 'Nothing
  Lookup (x ': xs) 'Z = 'Just x
  Lookup (x ': xs) ('S i) = Lookup xs i

-- | A type-level list of inhabitants, reflected to the value level with their indices.
type IndexedList :: forall k. [k] -> Type
data IndexedList as where
  FNil :: IndexedList '[]
  FCons :: forall a as. (KnownIndex a) => IndexedList as -> IndexedList (a ': as)

-- | An 'Indexed' kind with finitely many inhabitants, listed in 'Objects' in the order of their
-- indices: 'atLookup' says that the list tabulates 'At'.
class (Indexed k) => Finite k where
  type Objects k :: [k]
  finite :: IndexedList (Objects k)
  atLookup :: forall (i :: Nat). SNat i -> Lookup (Objects k) i :~: At k i

-- | A proof that @a@ occurs in the type-level list @as@.
type Member :: forall k. k -> [k] -> Type
data Member a as where
  Here :: Member a (a ': as)
  There :: Member a as -> Member a (b ': as)

-- | Every numbered inhabitant of a finite kind occurs in its list: walk to its index.
memberIndex :: forall {k} (a :: k). (Finite k, KnownIndex a) => Member a (Objects k)
memberIndex = case atLookup @k (snat @(Index a)) of
  Refl -> go (snat @(Index a)) (finite @k)
  where
    go :: forall i xs. (Lookup xs i ~ 'Just a) => SNat i -> IndexedList xs -> Member a xs
    go SZ (FCons _) = Here
    go (SS @i') (FCons xs) = There (go (snat @i') xs)

-- | A category on a 'Finite' kind whose objects are exactly its numbered inhabitants: 'withIndex'
-- and 'withOb' convert between the two notions.
type Enumerable :: Type -> Constraint
class (CategoryOf k, Finite k) => Enumerable k where
  withIndex :: forall (a :: k) r. (Ob a) => ((KnownIndex a) => r) -> r
  withOb :: forall (a :: k) r. (KnownIndex a) => ((Ob a) => r) -> r

-- | Locate an object in the object list.
member :: forall {k} (a :: k). (Enumerable k, Ob a) => Member a (Objects k)
member = withIndex @k @a (memberIndex @a)

instance Indexed BOOL where
  type Index FLS = 'Z
  type Index TRU = 'S 'Z
  type At BOOL 'Z = 'Just FLS
  type At BOOL ('S 'Z) = 'Just TRU
  type At BOOL ('S ('S i)) = 'Nothing

instance Finite BOOL where
  type Objects BOOL = '[FLS, TRU]
  finite = FCons (FCons FNil)
  atLookup SZ = Refl
  atLookup (SS @i) = case snat @i of
    SZ -> Refl
    SS -> Refl

instance Enumerable BOOL where
  withIndex @a r = case obj @a of
    Fls -> r
    Tru -> r
  withOb @a r = case snat @(Index a) of
    SZ -> r
    SS @i -> case snat @i of SZ -> r
