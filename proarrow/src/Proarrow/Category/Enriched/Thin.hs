{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Thin categories, where any two parallel arrows are equal: a 'ThinProfunctor' has at most one
-- element between any two objects, mere existence being captured by the constraint
-- @'HasArrow' p a b@. Also defines the codiscrete (always exactly one arrow) and discrete (only
-- identity arrows) special cases; 'DecidableProfunctor's, whose arrows are computed at the type
-- level as a 'BOOL' (the category thin profunctors are enriched in); and 'Enumerable' categories,
-- whose objects can be listed at the type level.
module Proarrow.Category.Enriched.Thin where

import Data.Kind (Constraint, Type)
import Prelude (type (~))

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

-- * Enumerable categories

-- | A proof that @a@ occurs in the type-level list @as@.
type Member :: forall k. k -> [k] -> Type
data Member a as where
  Here :: Member a (a ': as)
  There :: Member a as -> Member a (b ': as)

-- | A type-level list of objects, reflected to the value level with an 'Ob' proof for each element.
type ObjList :: forall k. [k] -> Type
data ObjList as where
  ONil :: ObjList '[]
  OCons :: forall a as. (Ob a) => ObjList as -> ObjList (a ': as)

-- | A category whose objects can be listed at the type level: 'Objects' names all of them,
-- 'objects' reflects that list to the value level, and 'member' locates any object in it.
type Enumerable :: Type -> Constraint
class (CategoryOf k) => Enumerable k where
  type Objects k :: [k]
  objects :: ObjList (Objects k)
  member :: forall (a :: k). (Ob a) => Member a (Objects k)

instance Enumerable BOOL where
  type Objects BOOL = '[FLS, TRU]
  objects = OCons (OCons ONil)
  member @a = case obj @a of
    Fls -> Here
    Tru -> There Here
