module Proarrow.Category.Bicategory.ThinCategoryAsBi where

import Prelude (type (~))

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.LaxFunctor (LaxFunctor (..), Map0, Map1, (:->))
import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..), dimapDefault, obj, type (+->))
import Proarrow.Profunctor.Representable (Representable (..), withObRep)

type THINK :: forall k -> CAT k
data THINK k i j = THIN

type ThinCategory :: CAT (THINK k i j)
data ThinCategory a b where
  Id :: forall {k} i j. (HasArrow (Hom k) i j, Ob i, Ob j) => ThinCategory (THIN :: THINK k (i :: k) (j :: k)) THIN

instance (Thin k) => Profunctor (ThinCategory :: CAT (THINK k i j)) where
  dimap = dimapDefault
  r \\ Id = r
instance (Thin k) => Promonad (ThinCategory :: CAT (THINK k i j)) where
  id = Id
  Id . Id = Id
instance (Thin k) => CategoryOf (THINK k i j) where
  type (~>) = ThinCategory
  type Ob (a :: THINK k i j) = (a ~ THIN, Ob i, Ob j, HasArrow (Hom k) i j)

instance (Thin k) => Bicategory (THINK k) where
  type Ob0 (THINK k) a = Ob a
  type I = THIN
  type O THIN THIN = THIN
  withOb2 @(_ :: THINK k j l) @(_ :: THINK k i j) r = withArr @(Hom k) @i @l (arr @(Hom k) @j @l . arr @(Hom k) @i @j) r
  withOb0s r = r
  r \\\ Id = r
  o @a @_ @c Id Id = withOb2 @(THINK k) @a @c Id
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @p @q @r = obj @p `o` obj @q `o` obj @r
  associatorInv @p @q @r = obj @p `o` obj @q `o` obj @r

-- | A functor between thin categories, i.e. a monotone function.
data family ThinFunctor (p :: j +-> k) :: THINK j :-> THINK k

type instance Map0 (ThinFunctor p) a = p % a
type instance Map1 (ThinFunctor p) THIN = THIN
instance (Representable p, Thin j, Thin k) => LaxFunctor (ThinFunctor (p :: j +-> k)) where
  map2 @a Id = withMap1Ob @(ThinFunctor p) @a Id
  laxId @i = withObRep @p @i Id
  laxComp @(THIN :: THINK j b c) @(THIN :: THINK j a b) =
    withArr (repMap @p (arr @_ @b @c) . repMap @p (arr @_ @a @b)) Id
  withMap0Ob0 @i r = withObRep @p @i r
  withMap1Ob @(THIN :: THINK j a b) r = withArr (repMap @p (arr @_ @a @b)) r