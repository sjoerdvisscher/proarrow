{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __collage__ (or cograph) of a profunctor @p@: a category on the disjoint union of @p@'s
-- two base categories ('L'- and 'R'-tagged objects, via the kind @'COLLAGE' p@), whose
-- cross-arrows @'L' a '~>' 'R' b@ are exactly the elements @p a b@ (the 'L2R' constructor).
-- The injections 'InjL'\/'InjR' present a profunctor as a single category sitting over the
-- walking arrow 'Proarrow.Category.Instance.Bool.BOOL'.
module Proarrow.Category.Instance.Collage where

import Data.Kind (Constraint)
import Data.List (genericIndex)
import Data.Type.Nat (SNat (..), SNatI, snat, type Plus)
import Prelude (Maybe (..), map, type (~))

import Proarrow.Category.Enriched.Finitary (Finitary (..))
import Proarrow.Category.Enriched.Thin
  ( AtOb (..)
  , CodiscreteProfunctor
  , Decidable
  , DecidableProfunctor (..)
  , Decision (..)
  , DiscreteProfunctor (..)
  , Enumerable (..)
  , Finite (..)
  , FmapWrap
  , Indexed (..)
  , IndexedList (..)
  , KnownIndex
  , Length
  , Lookup
  , MapWrap
  , Thin
  , ThinProfunctor (..)
  , anyArr
  , mapDecision
  , withAtLookup
  , withWrapAtLookup
  )
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Coproduct qualified as C
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Colimit.Initial (HasInitialObject (..), initiate')
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Hom
  , Kind
  , Obj
  , Profunctor (..)
  , Promonad (..)
  , dimapDefault
  , lmap
  , obj
  , rmap
  , type (+->)
  )
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..), terminate')
import Proarrow.Optic (iso)
import Proarrow.Optic.Iso (Iso')
import Proarrow.Profunctor.Instance.Direp (Direp (..))

type COLLAGE :: forall {j} {k}. k +-> j -> Kind
type data COLLAGE (p :: k +-> j) = L j | R k

type Collage :: CAT (COLLAGE p)
data Collage a b where
  InL :: a ~> b -> Collage (L a :: COLLAGE p) (L b :: COLLAGE p)
  InR :: a ~> b -> Collage (R a :: COLLAGE p) (R b :: COLLAGE p)
  L2R :: p a b -> Collage (L a :: COLLAGE p) (R b :: COLLAGE p)

type IsLR :: forall {p}. COLLAGE p -> Constraint
class IsLR (a :: COLLAGE p) where
  lrId :: Obj a
instance (Ob a, Promonad ((~>) :: CAT k)) => IsLR (L a :: (COLLAGE (p :: j +-> k))) where
  lrId = InL id
instance (Ob a, Promonad ((~>) :: CAT j)) => IsLR (R a :: (COLLAGE (p :: j +-> k))) where
  lrId = InR id

instance (Profunctor p) => Profunctor (Collage :: CAT (COLLAGE p)) where
  dimap = dimapDefault
  r \\ InL f = r \\ f
  r \\ InR f = r \\ f
  r \\ L2R p = r \\ p

instance (Profunctor p) => Promonad (Collage :: CAT (COLLAGE p)) where
  id = lrId
  InL g . InL f = InL (g . f)
  InR g . L2R p = L2R (rmap g p)
  L2R p . InL f = L2R (lmap f p)
  InR g . InR f = InR (g . f)

-- | The collage of a profunctor.
instance (Profunctor p) => CategoryOf (COLLAGE p) where
  type (~>) = Collage
  type Ob a = IsLR a

instance (HasInitialObject j, CategoryOf k, CodiscreteProfunctor p) => HasInitialObject (COLLAGE (p :: k +-> j)) where
  type InitialObject = L InitialObject
  initiate @a = case obj @a of
    InL a -> InL (initiate' a)
    InR b -> L2R anyArr \\ b

instance (HasTerminalObject k, CategoryOf j, CodiscreteProfunctor p) => HasTerminalObject (COLLAGE (p :: k +-> j)) where
  type TerminalObject = R TerminalObject
  terminate @a = case obj @a of
    InL a -> L2R anyArr \\ a
    InR b -> InR (terminate' b)

class HasArrowCollage p (a :: COLLAGE p) b where arrCoprod :: a ~> b
instance (Thin j, HasArrow (~>) (a :: j) b, Ob a, Ob b) => HasArrowCollage (p :: k +-> j) (L a) (L b) where
  arrCoprod = InL arr
instance (ThinProfunctor p, HasArrow p a b, Ob a, Ob b) => HasArrowCollage (p :: k +-> j) (L a) (R b) where
  arrCoprod = L2R arr
instance (Thin k, HasArrow (~>) (a :: k) b, Ob a, Ob b) => HasArrowCollage (p :: k +-> j) (R a) (R b) where
  arrCoprod = InR arr

instance (Thin j, Thin k, ThinProfunctor p) => ThinProfunctor (Collage :: CAT (COLLAGE (p :: k +-> j))) where
  type HasArrow (Collage :: CAT (COLLAGE p)) a b = HasArrowCollage p a b
  arr = arrCoprod
  withArr (InL f) r = withArr f r \\ f
  withArr (L2R p) r = withArr p r \\ p
  withArr (InR f) r = withArr f r \\ f

-- | Decided piecewise: within either side by that side's order, across by @p@, and never backwards.
instance
  (Decidable j, Decidable k, DecidableProfunctor p)
  => DecidableProfunctor (Collage :: CAT (COLLAGE (p :: k +-> j)))
  where
  type Holds (Collage :: CAT (COLLAGE (p :: k +-> j))) (L a) (L b) = Holds (Hom j) a b
  type Holds (Collage :: CAT (COLLAGE (p :: k +-> j))) (L a) (R b) = Holds p a b
  type Holds (Collage :: CAT (COLLAGE (p :: k +-> j))) (R a) (L b) = FLS
  type Holds (Collage :: CAT (COLLAGE (p :: k +-> j))) (R a) (R b) = Holds (Hom k) a b
  decide @x @y = case (obj @x, obj @y) of
    (InL @a f, InL @b g) -> mapDecision InL (decide @(Hom j) @a @b) \\ f \\ g
    (InL @a f, InR @b g) -> mapDecision L2R (decide @p @a @b) \\ f \\ g
    (InR _, InL _) -> No
    (InR @a f, InR @b g) -> mapDecision InR (decide @(Hom k) @a @b) \\ f \\ g
  toHolds (InL f) r = toHolds f r
  toHolds (L2R p) r = toHolds p r
  toHolds (InR f) r = toHolds f r

data family InjL :: forall (p :: k +-> j) -> j +-> COLLAGE p
instance (Profunctor p) => FunctorForRep (InjL p) where
  type InjL p @ a = L a
  fmap = InL

data family InjR :: forall (p :: k +-> j) -> k +-> COLLAGE p
instance (Profunctor p) => FunctorForRep (InjR p) where
  type InjR p @ a = R a
  fmap = InR

collageUniv :: forall {j} {k} (p :: k +-> j). (Profunctor p) => Iso' p (Direp (InjL p) (InjR p))
collageUniv = iso (Prof \p -> Direp (L2R p) \\ p) (Prof \case Direp (L2R q) -> q)

data family CollageAsCoprod :: COLLAGE (p :: k +-> j) +-> C.COPRODUCT j k
instance (DiscreteProfunctor p) => FunctorForRep (CollageAsCoprod :: COLLAGE (p :: k +-> j) +-> C.COPRODUCT j k) where
  type CollageAsCoprod @ L a = C.L a
  type CollageAsCoprod @ R a = C.R a
  fmap (InL f) = C.InjL f
  fmap (InR f) = C.InjR f
  fmap (L2R p) = exfalso p

data family ProjTo2 :: forall (p :: k +-> j) -> COLLAGE p +-> BOOL
instance (Profunctor p) => FunctorForRep (ProjTo2 p) where
  type ProjTo2 p @ L a = FLS
  type ProjTo2 p @ R a = TRU
  fmap = \case
    InL _ -> Fls
    InR _ -> Tru
    L2R _ -> F2T

-- * Numbering the collage

-- | The collage numbers the left category's objects first and the right category's after them.
type CollageObjects :: forall {j} {k}. forall (p :: k +-> j) -> [j] -> [COLLAGE p]
type family CollageObjects p xs where
  CollageObjects (p :: k +-> j) '[] = MapWrap R (Objects k)
  CollageObjects p (x ': xs) = L x ': CollageObjects p xs

instance (Finite j, Finite k) => Indexed (COLLAGE (p :: k +-> j)) where
  type Index (L a) = Index a
  type Index (R b :: COLLAGE (p :: k +-> j)) = Plus (Length (Objects j)) (Index b)

-- | An object of the left category is an object of the collage, keeping its index; one of the right
-- category is too, shifted past all the left ones. Both walk the left object list, and both hand the
-- fact to a continuation, since at each step the statement about the tail is the statement about the
-- whole list already reduced.
withCollageL
  :: forall {j} {k} (p :: k +-> j) (x :: j) r
   . (Finite j, Finite k, KnownIndex x)
  => ((KnownIndex (L x :: COLLAGE p)) => r) -> r
withCollageL r = withAtLookup @j (snat @(Index x)) (go (finite @j) (snat @(Index x)) r)
  where
    go
      :: forall xs i
       . (Lookup xs i ~ 'Just x)
      => IndexedList xs -> SNat i -> ((Lookup (CollageObjects p xs) i ~ 'Just (L x)) => r) -> r
    go (FCons _) SZ k = k
    go (FCons xs) (SS @i') k = go xs (snat @i') k

withCollageR
  :: forall {j} {k} (p :: k +-> j) (y :: k) r
   . (Finite j, Finite k, KnownIndex y)
  => ((KnownIndex (R y :: COLLAGE p)) => r) -> r
withCollageR r = go (finite @j) r
  where
    go
      :: forall xs
       . IndexedList xs
      -> ( ( SNatI (Plus (Length xs) (Index y))
           , Lookup (CollageObjects p xs) (Plus (Length xs) (Index y)) ~ FmapWrap R (At k (Index y))
           )
           => r
         )
      -> r
    go FNil k = withWrapAtLookup @(R :: k -> COLLAGE p) (snat @(Index y)) k
    go (FCons xs) k = go xs k

instance (Finite j, Finite k) => Finite (COLLAGE (p :: k +-> j)) where
  type Objects (COLLAGE (p :: k +-> j)) = CollageObjects p (Objects j)
  finite = goL (finite @j)
    where
      goL :: forall xs. IndexedList xs -> IndexedList (CollageObjects p xs)
      goL FNil = goR (finite @k)
      goL (FCons @x xs) = withCollageL @p @x (FCons @(L x) (goL xs))
      goR :: forall ys. IndexedList ys -> IndexedList (MapWrap (R :: k -> COLLAGE p) ys)
      goR FNil = FNil
      goR (FCons @y ys) = withCollageR @p @y (FCons @(R y) (goR ys))

-- | The collage of a finitary profunctor between finite categories is a finite category: a
-- hom-set is one of the two base hom-sets, or an element set of @p@ for a cross-arrow, or empty
-- going back the other way. Numbering it is numbering whichever of those it is.
--
-- A collage is the cheapest source of a category that is /not a poset/: @p@ can have several
-- elements between one pair of objects, and those are parallel arrows, while the base categories
-- supply whatever else is wanted. That is what a coverage on one is good for, and enumerating the
-- hom-sets is what any decision procedure over it needs.
instance
  (Finitary (Hom j), Finitary (Hom k), Finitary p)
  => Finitary (Collage :: CAT (COLLAGE (p :: k +-> j)))
  where
  size @a @b = case (obj @a, obj @b) of
    (InL @x f, InL @y g) -> size @(Hom j) @x @y \\ f \\ g
    (InL @x f, InR @y g) -> size @p @x @y \\ f \\ g
    (InR _, InL _) -> 0
    (InR @x f, InR @y g) -> size @(Hom k) @x @y \\ f \\ g
  toIndex = \case
    InL f -> toIndex f \\ f
    InR f -> toIndex f \\ f
    L2R x -> toIndex x \\ x
  fromIndex @a @b = genericIndex (elements @(Collage :: CAT (COLLAGE p)) @a @b)
  elements @a @b = case (obj @a, obj @b) of
    (InL @x f, InL @y g) -> map InL (elements @(Hom j) @x @y) \\ f \\ g
    (InL @x f, InR @y g) -> map L2R (elements @p @x @y) \\ f \\ g
    (InR _, InL _) -> []
    (InR @x f, InR @y g) -> map InR (elements @(Hom k) @x @y) \\ f \\ g

instance (Enumerable j, Enumerable k, Profunctor p) => Enumerable (COLLAGE (p :: k +-> j)) where
  withIndex @a r = case obj @a of
    InL @x f -> withIndex @j @x (withCollageL @p @x r) \\ f
    InR @y f -> withIndex @k @y (withCollageR @p @y r) \\ f
  atOb = go (finite @j)
    where
      go :: forall xs i. IndexedList xs -> SNat i -> AtOb (COLLAGE p) (Lookup (CollageObjects p xs) i)
      go FNil i = withWrapAtLookup @(R :: k -> COLLAGE p) i case atOb @k i of
        AtJust @_ @y -> withCollageR @p @y AtJust
        AtNothing -> AtNothing
      go (FCons @x _) SZ = withOb @j @x (withCollageL @p @x AtJust)
      go (FCons xs) (SS @i') = go xs (snat @i')
