module Proarrow.Category.Instance.IntConstruction where

import Prelude (type (~))

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , TracedMonoidal
  , par
  , swap
  , swapInner
  , trace
  , unitObj
  )
import Proarrow.Core (CAT, CategoryOf (..), Obj, Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Object.Exponential (Closed (..), CompactClosed (..), Dual, StarAutonomous (..))

type data Int k = I k k

type family IntPlus (i :: Int k) :: k where
  IntPlus (I a b) = a
type family IntMinus (i :: Int k) :: k where
  IntMinus (I a b) = b

type IntConstruction :: CAT (Int k)
data IntConstruction a b where
  Int :: (Ob ap, Ob am, Ob bp, Ob bm) => ap ** bm ~> am ** bp -> IntConstruction (I ap am) (I bp bm)

instance (SymMonoidal k, TracedMonoidal k) => Profunctor (IntConstruction :: CAT (Int k)) where
  dimap = dimapDefault
  r \\ Int{} = r
instance (SymMonoidal k, TracedMonoidal k) => Promonad (IntConstruction :: CAT (Int k)) where
  id @a = Int (swap @(IntPlus a) @(IntMinus a))
  Int @bp @bm @cp @cm f . Int @ap @am g = Int (trace @_ @(ap ** cm) @(am ** cp) @(bp ** bm) (_ . (f `par` g) . _))
instance (SymMonoidal k, TracedMonoidal k) => CategoryOf (Int k) where
  type (~>) = IntConstruction
  type Ob a = (a ~ I (IntPlus a) (IntMinus a), Ob (IntPlus a), Ob (IntMinus a))

instance (SymMonoidal k, TracedMonoidal k) => MonoidalProfunctor (IntConstruction :: CAT (Int k)) where
  par0 = Int (swap @Unit @Unit) \\ (unitObj :: Obj (Unit @(Int k)))
  Int @ap @am @bp @bm f `par` Int @cp @cm @dp @dm g = Int (swapInner @am @bp @cm @dp . (f `par` g) . swapInner @ap @cp @bm @dm)
instance (SymMonoidal k, TracedMonoidal k) => Monoidal (Int k) where
  type Unit = I Unit Unit
  type a ** b = I (IntPlus a ** IntPlus b) (IntMinus a ** IntMinus b)
instance (SymMonoidal k, TracedMonoidal k) => SymMonoidal (Int k) where
  Int @ap @am @bp @bm f `swap'` Int @cp @cm @dp @dm g = Int (_ . (f `par` g) . _)
instance (SymMonoidal k, TracedMonoidal k) => Closed (Int k) where
  type a ~~> b = I (IntMinus a) (IntPlus a) ** b
  curry' Int{} Int{} (Int f) = Int (_ f)
  uncurry' Int{} Int{} (Int f) = Int (_ f)
  Int f ^^^ Int g = Int (_ (f `par` g))
instance (SymMonoidal k, TracedMonoidal k) => StarAutonomous (Int k) where
  type Bottom = I Unit Unit
  bottomObj = unitObj
  doubleNeg' (Int f) = Int (_ f)
instance (SymMonoidal k, TracedMonoidal k) => CompactClosed (Int k) where
  distribDual' (Int a) (Int b) = Int (_ (a `par` b))
