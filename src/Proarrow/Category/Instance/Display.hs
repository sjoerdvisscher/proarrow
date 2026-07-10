{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Display where

import Data.Proxy (Proxy (..))
import Prelude (($), type (~))

import Data.Kind (Constraint)
import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.LaxFunctor (LaxFunctor (..), Map0, Map1, NormalLaxFunctor, type (:->))
import Proarrow.Category.Bicategory.Prof (PROFK (..), Prof (..))
import Proarrow.Category.Bicategory.ThinCategoryAsBi (THINK (..))
import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Profunctor.Composition ((:.:) (..))

data DISPLAY (f :: THINK k :-> PROFK) = forall (i :: k). D_ (Proxy i) (Map0 f i)

-- | Project the base object (the first component of the pair)
type family Base (d :: DISPLAY (f :: THINK k :-> PROFK)) :: k where
  Base (D_ ('Proxy @i) _) = i

type IsDisplay :: forall {k} {f :: THINK k :-> PROFK}. DISPLAY f -> Constraint
class (d ~ D_ ('Proxy :: Proxy (Base d)) (Fiber d)) => IsDisplay (d :: DISPLAY (f :: THINK k :-> PROFK)) where
  type Fiber d :: Map0 f (Base d)
instance IsDisplay (D_ ('Proxy :: Proxy x) a) where
  type Fiber (D_ ('Proxy :: Proxy x) a) = a

type D :: forall {k} (f :: THINK k :-> PROFK). forall (i :: k) -> Map0 f i -> DISPLAY f
type D i a = D_ ('Proxy @i) a

type Display :: CAT (DISPLAY f)
data Display a b where
  Display
    :: forall {k} {f} (i :: k) (j :: k) a b p
     . (p ~ UN PK (Map1 f (THIN :: THINK k i j)), Ob i, Ob j, NormalLaxFunctor f, HasArrow (Hom k) i j)
    => p a b -> Display (D j a :: DISPLAY f) (D i b :: DISPLAY f)

instance (Thin k) => Profunctor (Display :: CAT (DISPLAY (f :: THINK k :-> PROFK))) where
  dimap = dimapDefault
  r \\ Display @i @j p =
    withMap0Ob0 @f @i $
      withMap0Ob0 @f @j $
        withMap1Ob @f @(THIN :: THINK k i j) $
          r \\ p
instance (Thin k) => Promonad (Display :: CAT (DISPLAY (f :: THINK k :-> PROFK))) where
  id @a = Display (withMap0Ob0 @f @(Base a) $ withMap1Ob @f @(I :: THINK k (Base a) (Base a)) (unProf (laxId @f @(Base a))))
  Display m . Display n = Display (unProf (laxComp @f @THIN @THIN) (m :.: n))
instance (Thin k) => CategoryOf (DISPLAY (f :: THINK k :-> PROFK)) where
  type Ob @(DISPLAY f) a = (a ~ D (Base a) (Fiber a), Ob (Base a), Ob (Fiber a), NormalLaxFunctor f)
  type (~>) @(DISPLAY f) = Display @f
