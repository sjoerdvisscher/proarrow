module Proarrow.Category.Instance.IntConstruction where

import Prelude (type (~), ($))

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , TracedMonoidal
  , obj2
  , par
  , swap
  , swapFst
  , swapInner
  , swapOuter
  , trace
  )
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Object.Dual (CompactClosed (..), Dual, ExpSA, StarAutonomous (..), currySA, expSA, uncurrySA)
import Proarrow.Object.Exponential (Closed (..))

data INT k = I k k

type family IntPlus (i :: INT k) :: k where
  IntPlus (I a b) = a
type family IntMinus (i :: INT k) :: k where
  IntMinus (I a b) = b

type IntConstruction :: CAT (INT k)
data IntConstruction a b where
  Int :: (Ob ap, Ob am, Ob bp, Ob bm) => ap ** bm ~> am ** bp -> IntConstruction (I ap am) (I bp bm)

toInt :: forall {k} (a :: k) b. (TracedMonoidal k, Ob (Unit :: k)) => (a ~> b) -> I a Unit ~> I b Unit
toInt f = Int (swap @k @b @Unit . (f `par` obj @Unit)) \\ f

isoToInt :: forall {k} (a :: k) b. (TracedMonoidal k) => (a ~> b) -> (b ~> a) -> I a a ~> I b b
isoToInt f g = Int (swap @k @b @a . (f `par` g)) \\ f \\ g

fromInt :: forall {k} (a :: k) b m. (TracedMonoidal k) => (I a m ~> I b m) -> a ~> b
fromInt (Int f) = trace @(~>) @m @a @b (swap @k @m @b . f)

instance (TracedMonoidal k) => Profunctor (IntConstruction :: CAT (INT k)) where
  dimap = dimapDefault
  r \\ Int{} = r
instance (TracedMonoidal k) => Promonad (IntConstruction :: CAT (INT k)) where
  id @a = Int (swap @k @(IntPlus a) @(IntMinus a))
  Int @bp @bm @cp @cm f . Int @ap @am g =
    Int
      ( trace @_ @(bp ** bm) @(ap ** cm) @(am ** cp)
          (swapOuter @bm @cp @bp @am . (f `par` (swap @k @am @bp . g)) . swapFst @ap @cm @bp @bm)
      )
      \\ obj2 @ap @cm
      \\ obj2 @am @cp
      \\ obj2 @bp @bm
instance (TracedMonoidal k) => CategoryOf (INT k) where
  type (~>) = IntConstruction
  type Ob a = (a ~ I (IntPlus a) (IntMinus a), Ob (IntPlus a), Ob (IntMinus a))

instance (TracedMonoidal k, Ob (Unit :: k)) => MonoidalProfunctor (IntConstruction :: CAT (INT k)) where
  par0 = Int (swap @k @Unit @Unit)
  Int @ap @am @bp @bm f `par` Int @cp @cm @dp @dm g =
    Int (swapInner @am @bp @cm @dp . (f `par` g) . swapInner @ap @cp @bm @dm)
      \\ obj2 @(I ap am) @(I cp cm)
      \\ obj2 @(I bp bm) @(I dp dm)

instance (TracedMonoidal k, Ob (Unit :: k)) => Monoidal (INT k) where
  type Unit = I Unit Unit
  type a ** b = I (IntPlus a ** IntPlus b) (IntMinus a ** IntMinus b)
  withOb2 @a @b r = withOb2 @k @(IntPlus a) @(IntPlus b) (withOb2 @k @(IntMinus a) @(IntMinus b) r)
  leftUnitor @(I ap am) =
    Int ((leftUnitorInv @k @am `par` obj @ap) . swap @k @ap @am . (leftUnitor @k @ap `par` obj @am))
      \\ obj2 @Unit @ap
      \\ obj2 @Unit @am
  leftUnitorInv @(I ap am) =
    Int ((obj @am `par` leftUnitorInv @k @ap) . swap @k @ap @am . (obj @ap `par` leftUnitor @k @am))
      \\ obj2 @Unit @ap
      \\ obj2 @Unit @am
  rightUnitor @(I ap am) =
    Int ((rightUnitorInv @k @am `par` obj @ap) . swap @k @ap @am . (rightUnitor @k @ap `par` obj @am))
      \\ obj2 @ap @Unit
      \\ obj2 @am @Unit
  rightUnitorInv @(I ap am) =
    Int ((obj @am `par` rightUnitorInv @k @ap) . swap @k @ap @am . (obj @ap `par` rightUnitor @k @am))
      \\ obj2 @ap @Unit
      \\ obj2 @am @Unit
  associator @(I ap am) @(I bp bm) @(I cp cm) =
    Int (swap @k @(ap ** (bp ** cp)) @((am ** bm) ** cm) . (associator @k @ap @bp @cp `par` associatorInv @k @am @bm @cm))
      \\ obj2 @(I ap am) @(I bp bm) `par` obj @(I cp cm)
      \\ obj @(I ap am) `par` obj2 @(I bp bm) @(I cp cm)
  associatorInv @(I ap am) @(I bp bm) @(I cp cm) =
    Int (swap @k @((ap ** bp) ** cp) @(am ** (bm ** cm)) . (associatorInv @k @ap @bp @cp `par` associator @k @am @bm @cm))
      \\ obj2 @(I ap am) @(I bp bm) `par` obj @(I cp cm)
      \\ obj @(I ap am) `par` obj2 @(I bp bm) @(I cp cm)

instance (TracedMonoidal k, Ob (Unit :: k)) => SymMonoidal (INT k) where
  swap @(I ap am) @(I bp bm) = withOb2 @k @ap @bp $ withOb2 @k @am @bm $ withOb2 @k @bp @ap $ withOb2 @k @bm @am $
    Int ((swap @k @bm @am `par` swap @k @ap @bp) . swap @k @(ap ** bp) @(bm ** am))

instance (TracedMonoidal k, Ob (Unit :: k)) => Closed (INT k) where
  type a ~~> b = ExpSA a b
  curry' @a @b @c Int{} Int{} = currySA @a @b @c
  uncurry' @b @c Int{} Int{} = uncurrySA @_ @b @c
  (^^^) = expSA

instance (TracedMonoidal k, Ob (Unit :: k)) => StarAutonomous (INT k) where
  type Dual (I p n) = I n p
  dual (Int @ap @am @bp @bm f) = Int (swap @k @am @bp . f . swap @k @bm @ap)
  dualInv (Int @ap @am @bp @bm f) = Int (swap @k @am @bp . f . swap @k @bm @ap)
  linDist @(I ap am) @(I bp bm) @(I cp cm) (Int f) = Int (associator @k @am @bm @cm . f . associatorInv @k @ap @bp @cp) \\ obj2 @(I bp bm) @(I cp cm)
  linDistInv @(I ap am) @(I bp bm) @(I cp cm) (Int f) = Int (associatorInv @k @am @bm @cm . f . associator @k @ap @bp @cp) \\ obj2 @(I ap am) @(I bp bm)

instance (TracedMonoidal k, Ob (Unit :: k)) => CompactClosed (INT k) where
  distribDual @(I ap am) @(I bp bm) = Int (swap @k @(am ** bm) @(ap ** bp)) \\ obj2 @(I ap am) @(I bp bm)
  dualUnit = id
