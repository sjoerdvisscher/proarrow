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
import Data.Type.Nat (snat)
import Prelude (type (~))

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

type data DISCRETE k = D k

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

-- | An arrow of @'DISCRETE' k@ is an equality. This also witnesses that the category is discrete:
-- it only typechecks because 'Thin.withEq' demands it.
withEq :: forall {k} (a :: DISCRETE k) b r. (Thin.Indexed k) => Discrete a b -> ((a ~~ b) => r) -> r
withEq p r = Thin.withEq p r

-- | Two points are equal exactly when their indices are.
instance (Thin.Indexed k) => Thin.DecidableProfunctor (Discrete :: CAT (DISCRETE k)) where
  type Holds (Discrete :: CAT (DISCRETE k)) a b = Thin.Equal a b
  decide @a @b = Thin.mapDecision (\Eq.Refl -> Refl) (Thin.decideEq @a @b)
  toHolds @a Refl r = Thin.withNatEqRefl (snat @(Thin.Index a)) r

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
  underlying @a Refl = Thin.withNatEqRefl (snat @(Thin.Index a)) (obj @(Unit :: COST))
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

instance (Thin.Indexed k) => Thin.Indexed (DISCRETE k) where
  type Index (a :: DISCRETE k) = Thin.Index (UN D a)
  type At (DISCRETE k) i = Thin.FmapWrap D (Thin.At k i)

instance (Thin.Finite k) => Thin.Finite (DISCRETE k) where
  type Objects (DISCRETE k) = Thin.MapWrap D (Thin.Objects k)
  finite = Thin.wrapFinite @D
  withAtLookup = Thin.withWrapAtLookup @D

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

type data CODISCRETE k = CD k

type Codiscrete :: CAT (CODISCRETE k)
data Codiscrete a b where
  Arr :: (Ob a, Ob b) => Codiscrete a b

-- | The codiscrete category has exactly one arrow between any two objects, the numbered inhabitants
-- of @k@. Numbering them is what makes it enumerable, so that its closure can be computed.
instance (Thin.Indexed k) => CategoryOf (CODISCRETE k) where
  type (~>) = Codiscrete
  type Ob (a :: CODISCRETE k) = Thin.KnownIndex a

instance (Thin.Indexed k) => Profunctor (Codiscrete :: CAT (CODISCRETE k)) where
  dimap = dimapDefault
  r \\ Arr = r
instance (Thin.Indexed k) => Promonad (Codiscrete :: CAT (CODISCRETE k)) where
  id = Arr
  Arr . Arr = Arr

instance (Thin.Indexed k) => Thin.ThinProfunctor (Codiscrete :: CAT (CODISCRETE k))

instance (Thin.Indexed k) => Thin.DecidableProfunctor (Codiscrete :: CAT (CODISCRETE k)) where
  type Holds Codiscrete a b = TRU
  decide = Thin.Yes Arr
  toHolds Arr r = r

-- | Witnesses that @'CODISCRETE' k@ really is codiscrete: this only typechecks if 'Codiscrete' is a
-- 'Thin.CodiscreteProfunctor', so the definition is the check.
anyArr :: forall {k} (a :: CODISCRETE k) b. (Thin.Indexed k, Ob a, Ob b) => Codiscrete a b
anyArr = Thin.anyArr

instance (Thin.Indexed k) => Thin.Indexed (CODISCRETE k) where
  type Index (a :: CODISCRETE k) = Thin.Index (UN CD a)
  type At (CODISCRETE k) i = Thin.FmapWrap CD (Thin.At k i)

instance (Thin.Finite k) => Thin.Finite (CODISCRETE k) where
  type Objects (CODISCRETE k) = Thin.MapWrap CD (Thin.Objects k)
  finite = Thin.wrapFinite @CD
  withAtLookup = Thin.withWrapAtLookup @CD

instance (Thin.Finite k) => Thin.Enumerable (CODISCRETE k) where
  withIndex r = r
  withOb r = r

instance (Thin.Indexed k) => DaggerProfunctor (Codiscrete :: CAT (CODISCRETE k)) where
  dagger Arr = Arr

instance (Thin.Indexed k) => HasEqualizers (CODISCRETE k) where
  equalize = thinEqualize
  factorEqualizer Arr Arr = Arr

instance (Thin.Indexed k) => HasCoequalizers (CODISCRETE k) where
  coequalize = thinCoequalize
  factorCoequalizer Arr Arr = Arr

instance (Thin.Indexed k) => HasPullbacks (CODISCRETE k) where
  pullback @o Arr Arr k = k @o Arr Arr
  factorPullback Arr Arr Arr Arr = Arr

instance (Thin.Indexed k) => HasPushouts (CODISCRETE k) where
  pushout @o Arr Arr k = k @o Arr Arr
  factorPushout Arr Arr Arr Arr = Arr

instance (Thin.Indexed k) => HasEpiMonoFactorization (CODISCRETE k) where
  factorize = defaultFactorize

-- | Any object works as the product of any two objects here, since every hom-set is a singleton.
instance (Thin.Indexed k) => HasBinaryProducts (CODISCRETE k) where
  type a && b = a
  withObProd r = r
  fst = Arr
  snd = Arr
  Arr &&& Arr = Arr

-- | Dual to the 'HasBinaryProducts' instance above.
instance (Thin.Indexed k) => HasBinaryCoproducts (CODISCRETE k) where
  type a || b = a
  withObCoprod r = r
  lft = Arr
  rgt = Arr
  Arr ||| Arr = Arr
