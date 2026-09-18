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
import Proarrow.Category.Instance.Zero (Bottom (..), VOID, Zero)
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), VacuusOb, obj, type (+->))

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

instance (VacuusOb k, Hom k ~ (:~:)) => ThinProfunctor ((:~:) :: CAT k) where
  type HasArrow ((:~:) :: CAT k) a b = a ~ b
  arr = Refl
  withArr Refl r = r

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

-- | A profunctor that decides against an arrow has none, so a caller holding one may return anything.
noArrow :: forall {j} {k} (p :: j +-> k) a b r. (DecidableProfunctor p, Holds p a b ~ FLS) => p a b -> r
noArrow x = case eq of {}
  where
    eq :: Holds p a b :~: TRU
    eq = toHolds x Refl

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

  -- | A 'Finite' kind is numbered by its own object list: this default and the one for 'At' are
  -- inverse walks of 'Objects', so an instance that lists its inhabitants need say nothing here.
  type Index (a :: k) = IndexOf a (Objects k)

  type At k (i :: Nat) :: Maybe k
  type At k i = Lookup (Objects k) i

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

withNatEqRefl :: forall n r. SNat n -> ((NatEq n n ~ TRU) => r) -> r
withNatEqRefl SZ r = r
withNatEqRefl (SS @n') r = withNatEqRefl (snat @n') r

-- | Two numbered inhabitants are equal exactly when their indices are.
type Equal (a :: k) (b :: k) = NatEq (Index a) (Index b)

decideEq :: forall {k} (a :: k) b. (KnownIndex a, KnownIndex b) => Decision (:~:) a b (Equal a b)
decideEq = case natEq (snat @(Index a)) (snat @(Index b)) of
  Yes Refl -> Yes Refl
  No -> No

type Length :: [k] -> Nat
type family Length xs where
  Length '[] = 'Z
  Length (x ': xs) = 'S (Length xs)

type Lookup :: [k] -> Nat -> Maybe k
type family Lookup xs i where
  Lookup '[] i = 'Nothing
  Lookup (x ': xs) 'Z = 'Just x
  Lookup (x ': xs) ('S i) = Lookup xs i

-- | The inhabitant at an index in a type-level list known to be long enough: 'Lookup' without the
-- 'Maybe', for tables indexed by 'Index'. Out of range it is stuck rather than 'Nothing'.
type Entry :: [k] -> Nat -> k
type family Entry xs i where
  Entry (x ': xs) 'Z = x
  Entry (x ': xs) ('S i) = Entry xs i

-- | Every entry of @xs@ satisfies @c@. The list is shaped like @shape@, a list of objects, so that
-- an index into @shape@ selects an entry of @xs@. The equality argument ties the index to @shape@,
-- so that walking off the end is refutable rather than an error.
type KnownList :: forall {x} {y}. (x -> Constraint) -> [y] -> [x] -> Constraint
class KnownList c shape xs where
  withEntry :: forall s i r. SNat i -> Lookup shape i :~: 'Just s -> ((c (Entry xs i)) => r) -> r

instance KnownList c '[] '[] where
  withEntry _ eq _ = case eq of {}

instance (c x, KnownList c shape xs) => KnownList c (s ': shape) (x ': xs) where
  withEntry SZ Refl r = r
  withEntry (SS @i') eq r = withEntry @c @shape @xs (snat @i') eq r

-- | Where an inhabitant sits in a type-level list, the inverse of 'Lookup'. An inhabitant that does
-- not occur has no index, so the family is stuck rather than total.
type IndexOf :: forall k. k -> [k] -> Nat
type family IndexOf a xs where
  IndexOf a (a ': xs) = 'Z
  IndexOf a (b ': xs) = 'S (IndexOf a xs)

-- | A type-level list of inhabitants, reflected to the value level with their indices.
type IndexedList :: forall k. [k] -> Type
data IndexedList as where
  FNil :: IndexedList '[]
  FCons :: forall a as. (KnownIndex a) => IndexedList as -> IndexedList (a ': as)

-- | An 'Indexed' kind with finitely many inhabitants, listed in 'Objects' in the order of their
-- indices: 'withAtLookup' says that the list tabulates 'At'.
class (Indexed k) => Finite k where
  type Objects k :: [k]
  finite :: IndexedList (Objects k)
  withAtLookup :: forall (i :: Nat) r. SNat i -> ((Lookup (Objects k) i ~ At k i) => r) -> r
  default withAtLookup
    :: forall (i :: Nat) r. (At k i ~ Lookup (Objects k) i) => SNat i -> ((Lookup (Objects k) i ~ At k i) => r) -> r
  withAtLookup _ r = r

-- | A proof that @a@ occurs in the type-level list @as@.
type Member :: forall k. k -> [k] -> Type
data Member a as where
  Here :: Member a (a ': as)
  There :: Member a as -> Member a (b ': as)

-- | Every numbered inhabitant of a finite kind occurs in its list: walk to its index.
memberIndex :: forall {k} (a :: k). (Finite k, KnownIndex a) => Member a (Objects k)
memberIndex = withAtLookup @k (snat @(Index a)) (go (snat @(Index a)) (finite @k))
  where
    go :: forall i xs. (Lookup xs i ~ 'Just a) => SNat i -> IndexedList xs -> Member a xs
    go SZ (FCons _) = Here
    go (SS @i') (FCons xs) = There (go (snat @i') xs)

-- | A category on a 'Finite' kind whose objects are exactly its numbered inhabitants: 'withIndex'
-- and 'withOb' convert between the two notions, and 'atOb' looks an object up by its index.
type Enumerable :: Type -> Constraint
class (CategoryOf k, Finite k) => Enumerable k where
  withIndex :: forall (a :: k) r. (Ob a) => ((KnownIndex a) => r) -> r
  withOb :: forall (a :: k) r. (KnownIndex a) => ((Ob a) => r) -> r

  -- | The object at an index, if there is one. The default walks the object list, which is all a
  -- kind in general can do. A kind that can answer from the index alone should say so, and a wrapper
  -- kind whose base is itself 'Enumerable' should defer to it -- which the discrete kinds cannot,
  -- since they ask only that the kind they wrap be 'Finite'.
  atOb :: forall (i :: Nat). SNat i -> AtOb k (At k i)
  atOb i = withAtLookup @k i (lookupOb @k i (finite @k))

-- | Locate an object in the object list.
member :: forall {k} (a :: k). (Enumerable k, Ob a) => Member a (Objects k)
member = withIndex @k @a (memberIndex @a)

-- | Whether the inhabitant at an index exists, and if so that it is an object. Indexed by the lookup
-- itself, so that a caller holding @'At' k i ~ ''Just' a@ learns @'Ob' a@ -- which is what a wrapper
-- kind needs to recover the objects of the kind it wraps.
type AtOb :: forall k -> Maybe k -> Type
data AtOb k x where
  AtNothing :: AtOb k 'Nothing
  AtJust :: (Ob a, KnownIndex a) => AtOb k ('Just a)

-- | A numbered inhabitant is found at its own index, so evidence that nothing is there refutes
-- itself: under @'KnownIndex' a@ the argument's type is @''Just' a ':~:' ''Nothing'@, and a caller
-- holding one may return anything.
noIndex :: forall {k} (a :: k) r. (KnownIndex a) => At k (Index a) :~: 'Nothing -> r
noIndex eq = case eq of {}

-- | A kind that wraps another, one inhabitant for one, keeps its numbering: map the wrapper over the
-- lookup ('FmapWrap') and over the object list ('MapWrap'), and the two agree ('withLookupMapWrap').
type FmapWrap :: forall {j} {k}. (j -> k) -> Maybe j -> Maybe k
type family FmapWrap w x where
  FmapWrap w 'Nothing = 'Nothing
  FmapWrap w ('Just a) = 'Just (w a)

type MapWrap :: forall {j} {k}. (j -> k) -> [j] -> [k]
type family MapWrap w xs where
  MapWrap w '[] = '[]
  MapWrap w (x ': xs) = w x ': MapWrap w xs

mapWrap
  :: forall {j} {k} (w :: j -> k) xs
   . (forall (a :: j). (KnownIndex a) => KnownIndex (w a))
  => IndexedList xs -> IndexedList (MapWrap w xs)
mapWrap FNil = FNil
mapWrap (FCons @a xs) = FCons @(w a) (mapWrap @w xs)

withLookupMapWrap
  :: forall {j} {k} (w :: j -> k) xs i r
   . SNat i -> IndexedList xs -> ((Lookup (MapWrap w xs) i ~ FmapWrap w (Lookup xs i)) => r) -> r
withLookupMapWrap _ FNil r = r
withLookupMapWrap SZ (FCons _) r = r
withLookupMapWrap (SS @i') (FCons xs) r = withLookupMapWrap @w (snat @i') xs r

-- | The two 'Finite' methods of a wrapper kind, which are the same for every wrapper.
wrapFinite
  :: forall {j} {k} (w :: j -> k)
   . (Finite j, forall (a :: j). (KnownIndex a) => KnownIndex (w a))
  => IndexedList (MapWrap w (Objects j))
wrapFinite = mapWrap @w (finite @j)

withWrapAtLookup
  :: forall {j} {k} (w :: j -> k) i r
   . (Finite j)
  => SNat i -> ((Lookup (MapWrap w (Objects j)) i ~ FmapWrap w (At j i)) => r) -> r
withWrapAtLookup i r = withAtLookup @j i (withLookupMapWrap @w i (finite @j) r)

-- | The default 'atOb': walk the object list to the index.
lookupOb :: forall k (j :: Nat) xs. (Enumerable k) => SNat j -> IndexedList (xs :: [k]) -> AtOb k (Lookup xs j)
lookupOb _ FNil = AtNothing
lookupOb SZ (FCons @a _) = withOb @k @a AtJust
lookupOb (SS @j') (FCons xs) = lookupOb @k (snat @j') xs

instance Indexed BOOL where
  type Index FLS = 'Z
  type Index TRU = 'S 'Z
  type At BOOL i = Lookup '[FLS, TRU] i

instance Finite BOOL where
  type Objects BOOL = '[FLS, TRU]
  finite = FCons (FCons FNil)
  withAtLookup _ r = r

instance Enumerable BOOL where
  withIndex @a r = case obj @a of
    Fls -> r
    Tru -> r
  withOb @a r = case snat @(Index a) of
    SZ -> r
    SS @i -> case snat @i of SZ -> r

-- | The empty kind has no inhabitants to number.
instance Indexed VOID where
  type Index (a :: VOID) = 'Z
  type At VOID i = 'Nothing

instance Finite VOID where
  type Objects VOID = '[]
  finite = FNil
  withAtLookup _ r = r

instance Enumerable VOID where
  withIndex _ = no
  withOb @a _ = noIndex @a Refl
