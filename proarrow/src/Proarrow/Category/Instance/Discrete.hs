module Proarrow.Category.Instance.Discrete where

import Data.Type.Equality (type (~~))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin qualified as Thin
import Proarrow.Category.Topos (HasEpiMonoFactorization (..), defaultFactorize)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..), thinCoequalize)
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..), thinEqualize)
import Proarrow.Limit.Pullback (HasPullbacks (..))

newtype DISCRETE k = D k

type Discrete :: CAT (DISCRETE k)
data Discrete a b where
  Refl :: Discrete a a

-- | The discrete category with only identity arrows, every type of kind @k@ is an object.
instance CategoryOf (DISCRETE k) where
  type (~>) = Discrete

instance Profunctor Discrete where
  dimap = dimapDefault
instance Promonad Discrete where
  id = Refl
  Refl . Refl = Refl

instance Thin.ThinProfunctor Discrete where
  type HasArrow Discrete a b = (a ~~ b)
  arr = Refl
  withArr Refl r = r

withEq :: Discrete a b -> ((a ~~ b) => r) -> r
withEq p r = Thin.withEq p r

instance DaggerProfunctor Discrete where
  dagger Refl = Refl

instance HasEqualizers (DISCRETE k) where
  equalize = thinEqualize
  factorEqualizer Refl Refl = Refl

instance HasCoequalizers (DISCRETE k) where
  coequalize = thinCoequalize
  factorCoequalizer Refl Refl = Refl

instance HasPullbacks (DISCRETE k) where
  pullback Refl Refl k = k Refl Refl
  factorPullback Refl Refl Refl Refl = Refl

instance HasPushouts (DISCRETE k) where
  pushout Refl Refl k = k Refl Refl
  factorPushout Refl Refl Refl Refl = Refl

instance HasEpiMonoFactorization (DISCRETE k) where
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

instance Thin.ThinProfunctor Codiscrete where
  type HasArrow Codiscrete a b = ()
  arr = Arr
  withArr Arr r = r

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
