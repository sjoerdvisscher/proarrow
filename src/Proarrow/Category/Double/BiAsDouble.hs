{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Double.BiAsDouble where

import Proarrow.Category.Double (DOUBLE, Double(..))
import Proarrow.Category.Bicategory.Bidiscrete (VoidK, Bidiscrete (..))
import Proarrow.Category.Bicategory (Bicategory(..))
import Proarrow.Core (Promonad(..), CategoryOf(..))


type BiSq :: forall kk -> DOUBLE kk VoidK
data BiSq kk ps qs fs gs where
  BiSq :: ps ~> qs -> BiSq kk ps qs fs gs

-- | A bicategory as a double category with only identity arrows vertically.
instance Bicategory kk => Double kk VoidK where
  type Sq kk VoidK = BiSq kk
  object = BiSq id
  hArr = BiSq
  BiSq l ||| BiSq r = BiSq (r . l) \\\ l
  vArr Bidiscrete = BiSq id
  BiSq l === BiSq r = BiSq (l `o` r)


