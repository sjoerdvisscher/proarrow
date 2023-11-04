{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Double where

import Data.Kind (Type)

import Proarrow.Core (CategoryOf(..))
import Proarrow.Category.Bicategory (Path(..), type (+++), Bicategory(..), MKKIND)


-- h--i
-- |  |
-- j--k
type DOUBLE (hk :: MKKIND) (vk :: MKKIND) = forall {h} {i} {j} {k}. Path hk h i -> Path hk j k -> Path vk h j -> Path vk i k -> Type

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
  vArr :: (BiOb hk j, BiOb hk k) => (gs :: Path vk j k) ~> fs -> Sq hk vk Nil Nil fs gs
  -- | Vertical composition
  (===) :: Sq hk vk ps qs fs gs -> Sq hk vk rs ss gs hs -> Sq hk vk (ps +++ rs) (qs +++ ss) fs hs

type DOb hk vk k = (BiOb hk k, BiOb vk k)
