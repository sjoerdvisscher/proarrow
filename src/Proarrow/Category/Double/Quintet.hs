{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Double.Quintet where

import Data.Function (($))

import Proarrow.Core (CategoryOf(..), Promonad (..))
import Proarrow.Category.Double (DOUBLE, Double (..))
import Proarrow.Category.Bicategory (Path(..), appendObj, Bicategory (..), type (+++), withUnital, withAssoc)
import Proarrow.Category.Bicategory.Co (COK(..), UnCoPath, Co(..), unCoPathAppend)
import Proarrow.Object (obj)


type Quintet :: DOUBLE kk (COK kk)
data Quintet ps qs fs gs where
  Quintet
    :: forall {h} {i} {j} {k} {kk} ps qs fs gs
     . (Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob ps, Ob qs, Ob fs, Ob gs)
    => ps +++ UnCoPath gs ~> UnCoPath fs +++ qs
    -> Quintet (ps :: Path kk h j) (qs :: Path kk i k) (fs :: Path (COK kk) h i) (gs :: Path (COK kk) j k)

-- | The quintet construction. Create a double category of squares @alpha :: ps +++ gs ~> fs +++ qs@ from a bicategory.
instance Bicategory kk => Double kk (COK kk) where
  type Sq kk (COK kk) = Quintet
  object = Quintet id

  hArr :: forall {h} {j} (ps :: Path kk h j) qs. ps ~> qs -> Quintet ps qs Nil Nil
  hArr n = (withUnital @ps $ Quintet n) \\\ n

  vArr :: forall {h} {i} (fs :: Path (COK kk) h i) gs. fs ~> gs -> Quintet Nil Nil fs gs
  vArr (Co n) = (withUnital @(UnCoPath fs) $ Quintet n) \\\ n

  (|||) :: forall {h} {j} (ps :: Path kk h j) qs rs fs gs hs is. Quintet ps qs fs gs -> Quintet qs rs hs is -> Quintet ps rs (fs +++ hs) (gs +++ is)
  Quintet n ||| Quintet m = appendObj @fs @hs $ appendObj @gs @is $
    withAssoc @(UnCoPath fs) @(UnCoPath hs) @rs $ unCoPathAppend @fs @hs $
    withAssoc @(UnCoPath fs) @qs @(UnCoPath is) $
    withAssoc @ps @(UnCoPath gs) @(UnCoPath is) $ unCoPathAppend @gs @is $
      Quintet $ (obj @(UnCoPath fs) `o` m) . (n `o` obj @(UnCoPath is))

  (===) :: forall {h} {i} (ps :: Path kk h i) qs rs ss fs gs hs. Quintet ps qs fs gs -> Quintet rs ss gs hs -> Quintet (ps +++ rs) (qs +++ ss) fs hs
  Quintet n === Quintet m = appendObj @ps @rs $ appendObj @qs @ss $
    withAssoc @(UnCoPath fs) @qs @ss $ withAssoc @ps @(UnCoPath gs) @ss $ withAssoc @ps @rs @(UnCoPath hs) $
      Quintet $ (n `o` obj @ss) . (obj @ps `o` m)
