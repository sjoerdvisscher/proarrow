{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Double where

import Data.Kind (Type, Constraint)

import Proarrow.Core (CategoryOf(..))
import Proarrow.Category.Bicategory (Path(..), type (+++), Bicategory(..), MKKIND, obj1)
import Proarrow.Monad (RelMonad (..))


-- |
-- The kind of a square @p q f g@.
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--f--k
type DOUBLE (hk :: MKKIND) (vk :: MKKIND) = forall {h} {i} {j} {k}. Path hk h j -> Path hk i k -> Path vk h i -> Path vk j k -> Type

-- | Double categories, strictified in both directions.
class (Bicategory hk, Bicategory vk) => Double hk vk where
  type Sq hk vk :: DOUBLE hk vk
  -- | The empty square for an object.
  object :: DOb hk vk k => Sq hk vk (Nil :: Path hk k k) Nil Nil Nil
  -- | Make a square from a horizontal arrow
  hArr :: (BiOb vk j, BiOb vk k) => (ps :: Path hk j k) ~> qs -> Sq hk vk ps qs Nil Nil
  -- | Horizontal composition
  (|||) :: Sq hk vk ps qs fs gs -> Sq hk vk qs rs hs is -> Sq hk vk ps rs (fs +++ hs) (gs +++ is)
  -- | Make a square from a vertical arrow (in the opposite direction to match the quintet construction)
  vArr :: (BiOb hk j, BiOb hk k) => (fs :: Path vk j k) ~> gs -> Sq hk vk Nil Nil fs gs
  -- | Vertical composition
  (===) :: Sq hk vk ps qs fs gs -> Sq hk vk rs ss gs hs -> Sq hk vk (ps +++ rs) (qs +++ ss) fs hs

type DOb hk vk k = (BiOb hk k, BiOb vk k)

type family TmpOb (kk :: MKKIND) (p :: kk j k) :: Constraint

class (TmpOb hk (Companion hk vk f), TmpOb hk (Conjoint hk vk f)) => IsTmpOb hk vk f
instance (TmpOb hk (Companion hk vk f), TmpOb hk (Conjoint hk vk f)) => IsTmpOb hk vk f

class Double hk vk => Equipment hk vk where
  type Companion hk vk (f :: vk j k) :: hk j k
  type Conjoint hk vk (f :: vk j k) :: hk k j
  fromRight :: TmpOb vk f => Sq hk vk Nil (Companion hk vk f ::: Nil) Nil (f ::: Nil)
  toLeft :: TmpOb vk f => Sq hk vk (Companion hk vk f ::: Nil) Nil (f ::: Nil) Nil
  toRight :: TmpOb vk f => Sq hk vk Nil (Conjoint hk vk f ::: Nil) (f ::: Nil) Nil
  fromLeft :: TmpOb vk f => Sq hk vk (Conjoint hk vk f ::: Nil) Nil Nil (f ::: Nil)


-- +---+-j-+
-- |   | v |
-- | /<j</ |
-- | @ +---+
-- | \>t>\ |
-- |   | v |
-- +---+-t-+
unit
  :: forall {i} {k} {hk} {vk} (j :: vk i k) (t :: vk i k). (Equipment hk vk, BiOb vk i, BiOb vk k, TmpOb vk j, TmpOb vk t)
  => RelMonad (Companion hk vk j ::: Nil) (Conjoint hk vk t ::: Nil)
  -> Sq hk vk Nil Nil (j ::: Nil) (t ::: Nil)
unit m = hArr (return m) ||| (toLeft === fromLeft)

-- +-t-+---+--------+---+
-- | v |   |        |   |
-- | \>t>->t>\      |   |
-- |   +---+  \     |   |
-- |   | /<j<- \    |   |
-- |   | v |  \ \   |   |
-- |   +-j-+   \-@->t>\ |
-- |   | @ |    /   | | |
-- |   +-t-+   /    | | |
-- |   | v |  /     | | |
-- |   | \>t>/      | v |
-- +---+---+--------+-t-+
mult
  :: forall {i} {k} {hk} {vk} (j :: vk i k) (t :: vk i k). (Equipment hk vk, BiOb vk i, BiOb vk k, BiOb hk i, BiOb hk k, TmpOb vk j, TmpOb vk t, Ob (Conjoint hk vk t ::: Nil))
  => RelMonad (Companion hk vk j ::: Nil) (Conjoint hk vk t ::: Nil)
  -> Sq hk vk Nil Nil (j ::: Nil) (t ::: Nil)
  -> Sq hk vk Nil Nil (t ::: Nil) (t ::: Nil)
mult m jt = toRight ||| (hArr obj1 === fromRight === jt === toRight) ||| hArr (join m) ||| fromLeft