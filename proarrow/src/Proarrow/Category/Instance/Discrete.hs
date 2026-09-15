{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __discrete__ category on an 'Thin.Indexed' kind @k@ (@'DISCRETE' k@): the numbered inhabitants
-- of @k@ are the objects and the only arrows are identities ('Refl'). Numbering is what makes the
-- category decidable, and a 'Thin.Finite' kind gives an enumerable one, so that reachability along
-- a graph on a bare set of points can be computed. Its mirror image, the __codiscrete__ category
-- @CODISCRETE k@, has exactly one arrow between any two objects. All (co)limits that exist are
-- trivially computed.
module Proarrow.Category.Instance.Discrete where

import Data.Type.Equality (type (~~))
import Data.Type.Equality qualified as Eq
import Data.Type.Nat (SNat (..), snat)
import Prelude (Maybe (..), type (~))

import Proarrow.Category.Enriched (EnrichedProfunctor (..))
import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Enriched.Quantale (Quantale (..), bottomTensor)
import Proarrow.Category.Enriched.Thin qualified as Thin
import Proarrow.Category.Instance.Bool (BOOL (..), If)
import Proarrow.Category.Instance.Cost (COST)
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Topos (HasEpiMonoFactorization (..), defaultFactorize)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..), thinCoequalize)
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), UN, dimapDefault, obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..), thinEqualize)
import Proarrow.Limit.Pullback (HasPullbacks (..))

newtype DISCRETE k = D k

type Discrete :: CAT (DISCRETE k)
data Discrete a b where
  Refl :: (Ob a) => Discrete a a

-- | The discrete category with only identity arrows on the numbered inhabitants of @k@.
instance (Thin.Indexed k) => CategoryOf (DISCRETE k) where
  type (~>) = Discrete
  type Ob (a :: DISCRETE k) = Thin.KnownIndex a

instance (Thin.Indexed k) => Profunctor (Discrete :: CAT (DISCRETE k)) where
  dimap = dimapDefault
  r \\ Refl = r
instance (Thin.Indexed k) => Promonad (Discrete :: CAT (DISCRETE k)) where
  id = Refl
  Refl . Refl = Refl

instance (Thin.Indexed k) => Thin.ThinProfunctor (Discrete :: CAT (DISCRETE k)) where
  type HasArrow Discrete a b = (a ~~ b)
  arr = Refl
  withArr Refl r = r

withEq :: forall {k} (a :: DISCRETE k) b r. (Thin.Indexed k) => Discrete a b -> ((a ~~ b) => r) -> r
withEq p r = Thin.withEq p r

-- | Two points are equal exactly when their indices are.
instance (Thin.Indexed k) => Thin.DecidableProfunctor (Discrete :: CAT (DISCRETE k)) where
  type Holds (Discrete :: CAT (DISCRETE k)) a b = Thin.Equal a b
  decide @a @b = Thin.mapDecision (\Eq.Refl -> Refl) (Thin.decideEq @a @b)
  toHolds @a Refl r = case Thin.natEqRefl (snat @(Thin.Index a)) of Eq.Refl -> r

-- | The hom-object of the discrete category in a quantale: the unit on the diagonal, the bottom off
-- it. Points are at distance @0@ from themselves and infinitely far from each other: the discrete
-- category is a (discrete) Lawvere metric space, the base for shortest paths on a bare set of points.
type Delta :: forall (v :: Kind) -> BOOL -> v
type Delta v c = If c (Unit :: v) InitialObject

-- | The action of the discrete base on a matrix over the points: on the diagonal the 'Delta' is the
-- unit and the action is the unitor, off it the 'Delta' is the bottom and the action absorbs. The
-- argument says how the matrix is reindexed on the diagonal.
deltaAct
  :: forall {k} {v} (x :: k) y (w :: v) w'
   . (Quantale v, Thin.KnownIndex x, Thin.KnownIndex y, Ob w, Ob w')
  => ((x ~ y) => w Eq.:~: w') -> (Delta v (Thin.Equal x y) ** w) ~> w'
deltaAct eq = case Thin.decideEq @x @y of
  Thin.Yes Eq.Refl -> case eq of Eq.Refl -> leftUnitor @v @w
  Thin.No -> bottomTensor @w @w'

instance (Thin.Indexed k) => EnrichedProfunctor COST (Discrete :: CAT (DISCRETE k)) where
  type ProObj COST (Discrete :: CAT (DISCRETE k)) a b = Delta COST (Thin.Equal a b)
  withProObj @a @b r = case Thin.decideEq @a @b of
    Thin.Yes Eq.Refl -> r
    Thin.No -> r
  underlying @a Refl = case Thin.natEqRefl (snat @(Thin.Index a)) of Eq.Refl -> obj @(Unit :: COST)
  enriched @a @b f = case Thin.decideEq @a @b of
    Thin.Yes Eq.Refl -> Refl
    Thin.No -> unitIsNotBottom @COST f
  rmap @a @b @c =
    withProObj @COST @(Discrete :: CAT (DISCRETE k)) @a @b
      ( withProObj @COST @(Discrete :: CAT (DISCRETE k)) @a @c
          (deltaAct @b @c @(Delta COST (Thin.Equal a b)) @(Delta COST (Thin.Equal a c)) Eq.Refl)
      )
  lmap @a @b @c =
    withProObj @COST @(Discrete :: CAT (DISCRETE k)) @a @b
      ( withProObj @COST @(Discrete :: CAT (DISCRETE k)) @c @b
          (deltaAct @c @a @(Delta COST (Thin.Equal a b)) @(Delta COST (Thin.Equal c b)) Eq.Refl)
      )

type FmapD :: Maybe k -> Maybe (DISCRETE k)
type family FmapD m where
  FmapD 'Nothing = 'Nothing
  FmapD ('Just a) = 'Just (D a)

type MapD :: [k] -> [DISCRETE k]
type family MapD xs where
  MapD '[] = '[]
  MapD (x ': xs) = D x ': MapD xs

instance (Thin.Indexed k) => Thin.Indexed (DISCRETE k) where
  type Index (a :: DISCRETE k) = Thin.Index (UN D a)
  type At (DISCRETE k) i = FmapD (Thin.At k i)

instance (Thin.Finite k) => Thin.Finite (DISCRETE k) where
  type Objects (DISCRETE k) = MapD (Thin.Objects k)
  finite = mapD (Thin.finite @k)
  atLookup i = case Thin.atLookup @k i of Eq.Refl -> lookupMapD i (Thin.finite @k)

mapD :: Thin.IndexedList xs -> Thin.IndexedList (MapD xs)
mapD Thin.FNil = Thin.FNil
mapD (Thin.FCons xs) = Thin.FCons (mapD xs)

lookupMapD :: SNat i -> Thin.IndexedList xs -> Thin.Lookup (MapD xs) i Eq.:~: FmapD (Thin.Lookup xs i)
lookupMapD _ Thin.FNil = Eq.Refl
lookupMapD SZ (Thin.FCons _) = Eq.Refl
lookupMapD (SS @i) (Thin.FCons xs) = lookupMapD (snat @i) xs

instance (Thin.Finite k) => Thin.Enumerable (DISCRETE k) where
  withIndex r = r
  withOb r = r

instance (Thin.Indexed k) => DaggerProfunctor (Discrete :: CAT (DISCRETE k)) where
  dagger Refl = Refl

instance (Thin.Indexed k) => HasEqualizers (DISCRETE k) where
  equalize = thinEqualize
  factorEqualizer Refl Refl = Refl

instance (Thin.Indexed k) => HasCoequalizers (DISCRETE k) where
  coequalize = thinCoequalize
  factorCoequalizer Refl Refl = Refl

instance (Thin.Indexed k) => HasPullbacks (DISCRETE k) where
  pullback Refl Refl k = k Refl Refl
  factorPullback Refl Refl Refl Refl = Refl

instance (Thin.Indexed k) => HasPushouts (DISCRETE k) where
  pushout Refl Refl k = k Refl Refl
  factorPushout Refl Refl Refl Refl = Refl

instance (Thin.Indexed k) => HasEpiMonoFactorization (DISCRETE k) where
  factorize = defaultFactorize

newtype CODISCRETE k = CD k

type Codiscrete :: CAT (CODISCRETE k)
data Codiscrete a b where
  Arr :: Codiscrete a b

-- | The codiscrete category has exactly one arrow between every object, every type of kind @k@ is an object.
instance CategoryOf (CODISCRETE k) where
  type (~>) = Codiscrete

instance Profunctor Codiscrete where
  dimap = dimapDefault
instance Promonad Codiscrete where
  id = Arr
  Arr . Arr = Arr

instance Thin.ThinProfunctor Codiscrete

instance Thin.DecidableProfunctor Codiscrete where
  type Holds Codiscrete a b = TRU
  decide = Thin.Yes Arr
  toHolds Arr r = r

anyArr :: Codiscrete a b
anyArr = Thin.anyArr

instance DaggerProfunctor Codiscrete where
  dagger Arr = Arr

instance HasEqualizers (CODISCRETE k) where
  equalize = thinEqualize
  factorEqualizer _ _ = Arr

instance HasCoequalizers (CODISCRETE k) where
  coequalize = thinCoequalize
  factorCoequalizer _ _ = Arr

instance HasPullbacks (CODISCRETE k) where
  pullback @o _ _ k = k @o Arr Arr
  factorPullback _ _ _ _ = Arr

instance HasPushouts (CODISCRETE k) where
  pushout @o _ _ k = k @o Arr Arr
  factorPushout _ _ _ _ = Arr

instance HasEpiMonoFactorization (CODISCRETE k) where
  factorize = defaultFactorize

-- | Any object works as the product of any two objects here, since every hom-set is a singleton.
instance HasBinaryProducts (CODISCRETE k) where
  type a && b = a
  withObProd r = r
  fst = Arr
  snd = Arr
  _ &&& _ = Arr

-- | Dual to the 'HasBinaryProducts' instance above.
instance HasBinaryCoproducts (CODISCRETE k) where
  type a || b = a
  withObCoprod r = r
  lft = Arr
  rgt = Arr
  _ ||| _ = Arr
