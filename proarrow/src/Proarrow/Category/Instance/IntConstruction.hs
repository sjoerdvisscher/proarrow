{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | The __Int construction__ (Joyal-Street-Verity) on a traced monoidal category @k@: objects are
-- formal differences @'I' plus minus@ of @k@-objects, and morphisms are @k@-morphisms between the
-- appropriately tensored halves, composed by tracing out the middle. The result is compact closed
-- (the free such over @k@) with duals given by swapping the two halves.
module Proarrow.Category.Instance.IntConstruction where

import Prelude (($), type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), swap)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.StarAutonomous (ExpSA, StarAutonomous (..), applySA, currySA, expSA)
import Proarrow.Category.Monoidal.Strength (TracedMonoidal)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj, (\\))
import Proarrow.Tools.SMC (SYN (F, (:**)), lift, toSMC, (*))
import Proarrow.Tools.SMC qualified as SMC

data INT k = I k k

type family IntPlus (i :: INT k) :: k where
  IntPlus (I a b) = a
type family IntMinus (i :: INT k) :: k where
  IntMinus (I a b) = b

type IntConstruction :: CAT (INT k)
data IntConstruction a b where
  Int :: (Ob ap, Ob am, Ob bp, Ob bm) => ap ** bm ~> am ** bp -> IntConstruction (I ap am) (I bp bm)

toInt :: forall {k} (a :: k) b m. (TracedMonoidal k, Ob m) => (a ~> b) -> I a m ~> I b m
toInt f = Int (swap @k @b @m . (f ** obj @m)) \\ f

isoToInt :: forall {k} (a :: k) b. (TracedMonoidal k) => (a ~> b) -> (b ~> a) -> I a a ~> I b b
isoToInt f g = Int (swap @k @b @a . (f ** g)) \\ f \\ g

fromInt :: forall {k} (a :: k) b m. (TracedMonoidal k) => (I a m ~> I b m) -> a ~> b
fromInt (Int f) = toSMC @(F a) \a -> SMC.do
  let f' = lift @(F a :** F m) @(F m :** F b) f
  rec (m, b) <- f' (a * m)
  b

instance (TracedMonoidal k) => Profunctor (IntConstruction :: CAT (INT k)) where
  dimap = dimapDefault
  r \\ Int{} = r
instance (TracedMonoidal k) => Promonad (IntConstruction :: CAT (INT k)) where
  id @a = Int (swap @k @(IntPlus a) @(IntMinus a))
  Int @bp @bm @cp @cm f . Int @ap @am g =
    Int $ toSMC @(F ap :** F cm) \x -> SMC.do
      let g' = lift @(F ap :** F bm) @(F am :** F bp) g
          f' = lift @(F bp :** F cm) @(F bm :** F cp) f
      (ap, cm) <- x
      rec ((am, bp), (bm, cp)) <- g' (ap * bm) * f' (bp * cm)
      am * cp

-- | The Int construction, a.k.a. the geometry of interaction,
-- the free compact closed category on a traced monoidal category.
instance (TracedMonoidal k) => CategoryOf (INT k) where
  type (~>) = IntConstruction
  type Ob a = (a ~ I (IntPlus a) (IntMinus a), Ob (IntPlus a), Ob (IntMinus a))

instance (TracedMonoidal k) => MonoidalProfunctor (IntConstruction :: CAT (INT k)) where
  one = Int (swap @k @Unit @Unit)
  Int @ap @am @bp @bm f ** Int @cp @cm @dp @dm g =
    withOb2 @(INT k) @(I ap am) @(I cp cm) $
      withOb2 @(INT k) @(I bp bm) @(I dp dm) $
        Int $ toSMC @((F ap :** F cp) :** (F bm :** F dm)) \x -> SMC.do
          let f' = lift @(F ap :** F bm) @(F am :** F bp) f
              g' = lift @(F cp :** F dm) @(F cm :** F dp) g
          ((ap, cp), (bm, dm)) <- x
          (am, bp) <- f' (ap * bm)
          (cm, dp) <- g' (cp * dm)
          (am * cm) * (bp * dp)

-- | The monoidal tensor is pointwise, tensoring of the plus and minus parts.
instance (TracedMonoidal k) => Monoidal (INT k) where
  type Unit = I Unit Unit
  type a ** b = I (IntPlus a ** IntPlus b) (IntMinus a ** IntMinus b)
  withOb2 @a @b r = withOb2 @k @(IntPlus a) @(IntPlus b) (withOb2 @k @(IntMinus a) @(IntMinus b) r)
  leftUnitor @(I ap am) =
    withOb2 @k @Unit @ap $
      withOb2 @k @Unit @am $
        Int ((leftUnitorInv @k @am ** obj @ap) . swap @k @ap @am . (leftUnitor @k @ap ** obj @am))
  leftUnitorInv @(I ap am) =
    withOb2 @k @Unit @ap $
      withOb2 @k @Unit @am $
        Int ((obj @am ** leftUnitorInv @k @ap) . swap @k @ap @am . (obj @ap ** leftUnitor @k @am))
  rightUnitor @(I ap am) =
    withOb2 @k @ap @Unit $
      withOb2 @k @am @Unit $
        Int ((rightUnitorInv @k @am ** obj @ap) . swap @k @ap @am . (rightUnitor @k @ap ** obj @am))
  rightUnitorInv @(I ap am) =
    withOb2 @k @ap @Unit $
      withOb2 @k @am @Unit $
        Int ((obj @am ** rightUnitorInv @k @ap) . swap @k @ap @am . (obj @ap ** rightUnitor @k @am))
  associator @(I ap am) @(I bp bm) @(I cp cm) =
    withOb2 @(INT k) @(I ap am) @(I bp bm) $
      withOb2 @(INT k) @(I ap am ** I bp bm) @(I cp cm) $
        withOb2 @(INT k) @(I bp bm) @(I cp cm) $
          withOb2 @(INT k) @(I ap am) @(I bp bm ** I cp cm) $
            Int
              ( swap @k @(ap ** (bp ** cp)) @((am ** bm) ** cm)
                  . (associator @k @ap @bp @cp ** associatorInv @k @am @bm @cm)
              )
  associatorInv @(I ap am) @(I bp bm) @(I cp cm) =
    withOb2 @(INT k) @(I ap am) @(I bp bm) $
      withOb2 @(INT k) @(I ap am ** I bp bm) @(I cp cm) $
        withOb2 @(INT k) @(I bp bm) @(I cp cm) $
          withOb2 @(INT k) @(I ap am) @(I bp bm ** I cp cm) $
            Int
              ( swap @k @((ap ** bp) ** cp) @(am ** (bm ** cm))
                  . (associatorInv @k @ap @bp @cp ** associator @k @am @bm @cm)
              )

instance (TracedMonoidal k) => SymMonoidal (INT k) where
  swap @(I ap am) @(I bp bm) =
    withOb2 @k @ap @bp $
      withOb2 @k @am @bm $
        withOb2 @k @bp @ap $
          withOb2 @k @bm @am $
            Int ((swap @k @bm @am ** swap @k @ap @bp) . swap @k @(ap ** bp) @(bm ** am))

instance (TracedMonoidal k) => Closed (INT k) where
  type a ~~> b = ExpSA a b
  withObExp @a @b r = withOb2 @k @(IntMinus a) @(IntPlus b) (withOb2 @k @(IntPlus a) @(IntMinus b) r)
  curry @a @b @c = currySA @a @b @c
  apply @b @c = applySA @b @c
  (^^^) = expSA

instance (TracedMonoidal k) => StarAutonomous (INT k) where
  type Dual (I p n) = I n p
  withObDual r = r
  dual (Int @ap @am @bp @bm f) = Int (swap @k @am @bp . f . swap @k @bm @ap)
  dualInv (Int @ap @am @bp @bm f) = Int (swap @k @am @bp . f . swap @k @bm @ap)
  linDist @(I ap am) @(I bp bm) @(I cp cm) (Int f) =
    withOb2 @(INT k) @(I bp bm) @(I cp cm) (Int (associator @k @am @bm @cm . f . associatorInv @k @ap @bp @cp))
  linDistInv @(I ap am) @(I bp bm) @(I cp cm) (Int f) =
    withOb2 @(INT k) @(I ap am) @(I bp bm) (Int (associatorInv @k @am @bm @cm . f . associator @k @ap @bp @cp))
  doubleNeg = id
  doubleNegInv = id

instance (TracedMonoidal k) => CompactClosed (INT k) where
  distribDual @(I ap am) @(I bp bm) = withOb2 @(INT k) @(I ap am) @(I bp bm) (Int (swap @k @(am ** bm) @(ap ** bp)))
  dualUnit = id
  dualityUnit @(I p n) =
    withOb2 @k @p @n $ withOb2 @k @n @p $ Int (leftUnitorInv @k @(p ** n) . swap @k @n @p . leftUnitor @k @(n ** p))
  dualityCounit @(I p n) =
    withOb2 @k @p @n $ withOb2 @k @n @p $ Int (rightUnitorInv @k @(p ** n) . swap @k @n @p . rightUnitor @k @(n ** p))
