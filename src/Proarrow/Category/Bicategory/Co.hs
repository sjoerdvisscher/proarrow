module Proarrow.Category.Bicategory.Co where

import Proarrow.Category.Bicategory
  ( Adjunction (..)
  , Bicategory (..)
  , Comonad (..)
  , Monad (..)
  )
import Proarrow.Category.Bicategory.Kan
  ( LeftKanExtension (..)
  , LeftKanLift (..)
  , RightKanExtension (..)
  , RightKanLift (..)
  )
import Proarrow.Category.Equipment (Cotight, CotightAdjoint, Equipment (..), IsOb, Tight, TightAdjoint, WithObO2 (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type COK :: CAT k -> CAT k
newtype COK kk j k = CO (kk j k)
type instance UN CO (CO k) = k

type Co :: CAT (COK kk j k)
data Co a b where
  Co :: b ~> a -> Co (CO a) (CO b)

instance (CategoryOf (kk j k)) => Profunctor (Co :: CAT (COK kk j k)) where
  dimap = dimapDefault
  r \\ Co f = r \\ f
instance (CategoryOf (kk j k)) => Promonad (Co :: CAT (COK kk j k)) where
  id = Co id
  Co f . Co g = Co (g . f)
instance (CategoryOf (kk j k)) => CategoryOf (COK kk j k) where
  type (~>) = Co
  type Ob a = (Is CO a, Ob (UN CO a))

-- | Create a dual of a bicategory by reversing the 2-cells.
instance (Bicategory kk) => Bicategory (COK kk) where
  type Ob0 (COK kk) k = Ob0 kk k
  type I = CO I
  type a `O` b = CO (UN CO a `O` UN CO b)
  withOb2 @(CO a) @(CO b) r = withOb2 @kk @a @b r
  withOb0s @(CO a) r = withOb0s @kk @a r
  r \\\ Co f = r \\\ f
  Co f `o` Co g = Co (f `o` g)
  leftUnitor = Co leftUnitorInv
  leftUnitorInv = Co leftUnitor
  rightUnitor = Co rightUnitorInv
  rightUnitorInv = Co rightUnitor
  associator @(CO p) @(CO q) @(CO r) = Co (associatorInv @kk @p @q @r)
  associatorInv @(CO p) @(CO q) @(CO r) = Co (associator @kk @p @q @r)

type instance IsOb Tight p = IsOb Cotight (UN CO p)
type instance IsOb Cotight p = IsOb Tight (UN CO p)
type instance TightAdjoint p = CO (CotightAdjoint (UN CO p))
type instance CotightAdjoint p = CO (TightAdjoint (UN CO p))
instance (WithObO2 Cotight kk) => WithObO2 Tight (COK kk) where
  withObO2 @p @q r = withObO2 @Cotight @kk @(UN CO p) @(UN CO q) r
instance (WithObO2 Tight kk) => WithObO2 Cotight (COK kk) where
  withObO2 @p @q r = withObO2 @Tight @kk @(UN CO p) @(UN CO q) r
instance (Equipment kk) => Equipment (COK kk) where
  withTightAdjoint @(CO f) r = withCotightAdjoint @kk @f r
  withCotightAdjoint @(CO f) r = withTightAdjoint @kk @f r

instance (Adjunction f g) => Adjunction (CO g) (CO f) where
  unit = Co (counit @f @g)
  counit = Co (unit @f @g)

instance (Comonad m) => Monad (CO m) where
  eta = Co epsilon
  mu = Co delta

instance (Monad m) => Comonad (CO m) where
  epsilon = Co eta
  delta = Co mu

instance (RightKanExtension j f) => LeftKanExtension (CO j) (CO f) where
  type Lan (CO j) (CO f) = CO (Ran j f)
  lan = Co (ran @j @f)
  lanUniv (Co n) = Co (ranUniv @j @f n)

instance (LeftKanExtension j f) => RightKanExtension (CO j) (CO f) where
  type Ran (CO j) (CO f) = CO (Lan j f)
  ran = Co (lan @j @f)
  ranUniv (Co n) = Co (lanUniv @j @f n)

instance (RightKanLift j f) => LeftKanLift (CO j) (CO f) where
  type Lift (CO j) (CO f) = CO (Rift j f)
  lift = Co (rift @j @f)
  liftUniv (Co n) = Co (riftUniv @j @f n)

instance (LeftKanLift j f) => RightKanLift (CO j) (CO f) where
  type Rift (CO j) (CO f) = CO (Lift j f)
  rift = Co (lift @j @f)
  riftUniv (Co n) = Co (liftUniv @j @f n)
