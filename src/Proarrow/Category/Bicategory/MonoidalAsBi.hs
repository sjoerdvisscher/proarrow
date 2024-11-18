module Proarrow.Category.Bicategory.MonoidalAsBi where

import Prelude (type (~))

import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..), Comonad (..), Monad (..))
import Proarrow.Category.Bicategory.Kan (LeftKanExtension (..), RightKanExtension (..), RightKanLift (..), LeftKanLift (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..))
import Proarrow.Category.Monoidal (SymMonoidal)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, obj)
import Proarrow.Monoid qualified as M
import Proarrow.Object.Coexponential (Coclosed (..), coeval, coevalUniv)
import Proarrow.Object.Exponential (Closed (..), curry, eval)
import Proarrow.Object.Exponential qualified as M
import Proarrow.Category.Equipment.Limit (HasLimits (..), HasColimits (..))

type MonK :: Kind -> CAT ()
newtype MonK k i j = MK k
type instance UN MK (MK k) = k

type Mon2 :: forall {k} {i} {j}. CAT (MonK k i j)
data Mon2 a b where
  Mon2 :: a ~> b -> Mon2 (MK a) (MK b)
  deriving (Profunctor, Promonad) via (~>)

instance (CategoryOf k) => CategoryOf (MonK k i j) where
  type (~>) = Mon2
  type Ob a = (Is MK a, Ob (UN MK a))

-- | A monoidal category as a bicategory.
instance (M.Monoidal k) => Bicategory (MonK k) where
  type I = MK M.Unit
  type MK a `O` MK b = MK (a M.** b)
  iObj = Mon2 M.par0
  Mon2 f `o` Mon2 g = Mon2 (f `M.par` g)
  r \\\ Mon2 f = r \\ f
  leftUnitor (Mon2 p) = Mon2 (M.leftUnitor p)
  leftUnitorInv (Mon2 p) = Mon2 (M.leftUnitorInv p)
  rightUnitor (Mon2 p) = Mon2 (M.rightUnitor p)
  rightUnitorInv (Mon2 p) = Mon2 (M.rightUnitorInv p)
  associator (Mon2 p) (Mon2 q) (Mon2 r) = Mon2 (M.associator p q r)
  associatorInv (Mon2 p) (Mon2 q) (Mon2 r) = Mon2 (M.associatorInv p q r)

-- | Monoids in a monoidal category are monads when the monoidal category is seen as a bicategory.
instance (M.Monoid m) => Monad (MK m) where
  eta = Mon2 M.mempty
  mu = Mon2 M.mappend

-- | Comonoids in a monoidal category are comonads when the monoidal category is seen as a bicategory.
instance (M.Comonoid m) => Comonad (MK m) where
  epsilon = Mon2 M.counit
  delta = Mon2 M.comult

instance (M.Monoidal k) => HasCompanions (MonK k) (MonK k) where
  type Companion (MonK k) (MonK k) (MK a) = MK a
  mapCompanion (Mon2 f) = Mon2 f
  compToId = Mon2 M.unitObj
  compFromId = Mon2 M.unitObj
  compToCompose (Mon2 f) (Mon2 g) = Mon2 (f `M.par` g)
  compFromCompose (Mon2 f) (Mon2 g) = Mon2 (f `M.par` g)

instance (M.CompactClosed k, Ob (a :: k), b ~ M.Dual a) => Adjunction (MK a) (MK b) where
  unit = Mon2 (M.swap @a @b . M.dualityUnit @a) \\ M.dualObj @a
  counit = Mon2 (M.dualityCounit @a . M.swap @a @b) \\ M.dualObj @a

instance (M.CompactClosed k) => Equipment (MonK k) (MonK k) where
  type Conjoint (MonK k) (MonK k) (MK a) = MK (M.Dual a)
  mapConjoint (Mon2 f) = Mon2 (M.dual f)
  conjToId = Mon2 (M.eval @M.Unit . M.rightUnitorInv (M.dualObj @M.Unit)) \\ M.unitObj @k
  conjFromId = Mon2 (M.mkExponential M.unitObj)
  conjToCompose (Mon2 f) (Mon2 g) = Mon2 (M.distribDual' g f . (M.dual (g `M.swap'` f)))
  conjFromCompose (Mon2 f) (Mon2 g) = Mon2 ((M.dual (f `M.swap'` g)) . M.combineDual' g f)

instance (Closed k, Ob j) => HasLimits (MonK k) (MK (j :: k)) '() where
  type Limit (MK j) (MK d) = MK (j ~~> d)
  limitObj @(MK d) = Mon2 (obj @d ^^^ obj @j)
  limit @(MK d) = Mon2 (eval @j @d)
  limitUniv @_ @(MK p) (Mon2 pj2d) = Mon2 (curry @p @j pj2d)

instance (M.Monoidal k, Ob j) => HasColimits (MonK k) (MK (j :: k)) '() where
  type Colimit (MK j) (MK d) = MK (d M.** j)
  colimit @(MK d) = Mon2 (obj @d `M.par` obj @j)
  colimitUniv (Mon2 f) = Mon2 f

instance (Closed k, Ob (p ~~> q), Ob p, Ob q) => RightKanExtension (MK (p :: k)) (MK (q :: k)) where
  type Ran (MK p) (MK q) = MK (p ~~> q)
  ran = Mon2 (eval @p @q)
  ranUniv @(MK g) (Mon2 f) = Mon2 (curry @g @p @q f)

instance (Closed k, SymMonoidal k, Ob (p ~~> q), Ob p, Ob q) => RightKanLift (MK (p :: k)) (MK (q :: k)) where
  type Rift (MK p) (MK q) = MK (p ~~> q)
  rift = Mon2 (eval @p @q . M.swap @p @(p ~~> q))
  riftUniv @(MK g) (Mon2 f) = Mon2 (curry @g @p @q (f . M.swap @g @p))

instance (Coclosed k, Ob (q <~~ p), Ob p, Ob q) => LeftKanExtension (MK (p :: k)) (MK (q :: k)) where
  type Lan (MK p) (MK q) = MK (q <~~ p)
  lan = Mon2 (coeval @q @p)
  lanUniv @(MK g) (Mon2 f) = Mon2 (coevalUniv @q @p @g f)

instance (Coclosed k, SymMonoidal k, Ob (q <~~ p), Ob p, Ob q) => LeftKanLift (MK (p :: k)) (MK (q :: k)) where
  type Lift (MK p) (MK q) = MK (q <~~ p)
  lift = Mon2 (M.swap @(q <~~ p) @p . coeval @q @p)
  liftUniv @(MK g) (Mon2 f) = Mon2 (coevalUniv @q @p @g (M.swap @p @g . f))
