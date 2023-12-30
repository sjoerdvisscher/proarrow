{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Double where

import Data.Kind (Type)

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
  hArr :: (Ob0 vk j, Ob0 vk k) => (ps :: Path hk j k) ~> qs -> Sq hk vk ps qs Nil Nil
  -- | Horizontal composition
  (|||) :: Sq hk vk ps qs fs gs -> Sq hk vk qs rs hs is -> Sq hk vk ps rs (fs +++ hs) (gs +++ is)
  -- | Make a square from a vertical arrow (in the opposite direction to match the quintet construction)
  vArr :: (Ob0 hk j, Ob0 hk k) => (fs :: Path vk j k) ~> gs -> Sq hk vk Nil Nil fs gs
  -- | Vertical composition
  (===) :: Sq hk vk ps qs fs gs -> Sq hk vk rs ss gs hs -> Sq hk vk (ps +++ rs) (qs +++ ss) fs hs

type DOb hk vk k = (Ob0 hk k, Ob0 vk k)

class Double hk vk => Equipment hk vk where
  type Companion hk vk (f :: vk j k) :: hk j k
  type Conjoint hk vk (f :: vk j k) :: hk k j
  fromRight :: Ob1 vk f => Sq hk vk Nil (Companion hk vk f ::: Nil) Nil (f ::: Nil)
  toLeft :: Ob1 vk f => Sq hk vk (Companion hk vk f ::: Nil) Nil (f ::: Nil) Nil
  toRight :: Ob1 vk f => Sq hk vk Nil (Conjoint hk vk f ::: Nil) (f ::: Nil) Nil
  fromLeft :: Ob1 vk f => Sq hk vk (Conjoint hk vk f ::: Nil) Nil Nil (f ::: Nil)


-- +---+-j-+
-- |   | v |
-- | /<j</ |
-- | @ +---+
-- | \>t>\ |
-- |   | v |
-- +---+-t-+
unit
  :: forall {i} {k} {hk} {vk} (j :: vk i k) (t :: vk i k). (Equipment hk vk, Ob0 vk i, Ob0 vk k, Ob1 vk j, Ob1 vk t)
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
  :: forall {i} {k} {hk} {vk} (j :: vk i k) (t :: vk i k). (Equipment hk vk, Ob0 vk i, Ob0 vk k, Ob0 hk i, Ob0 hk k, Ob1 vk j, Ob1 vk t, Ob (Conjoint hk vk t ::: Nil))
  => RelMonad (Companion hk vk j ::: Nil) (Conjoint hk vk t ::: Nil)
  -> Sq hk vk Nil Nil (j ::: Nil) (t ::: Nil)
  -> Sq hk vk Nil Nil (t ::: Nil) (t ::: Nil)
mult m jt = toRight ||| (hArr obj1 === fromRight === jt === toRight) ||| hArr (join m) ||| fromLeft