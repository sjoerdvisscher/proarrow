{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Double.BiAsDouble where

import Proarrow.Category.Bicategory (Bicategory (..), Path (..), Strictified (..))
import Proarrow.Category.Bicategory.Bidiscrete (Bidiscrete (..), DiscreteK)
import Proarrow.Category.Double (DOUBLE, Double (..))
import Proarrow.Core (CategoryOf (..), Promonad (..))

type BiSq :: forall kk -> DOUBLE kk DiscreteK
data BiSq kk ps qs fs gs where
  BiSq :: ps ~> qs -> BiSq kk ps qs Nil Nil

-- | A bicategory as a double category with only identity arrows vertically.
instance (Bicategory kk) => Double kk DiscreteK where
  type Sq kk DiscreteK = BiSq kk
  object = BiSq id
  hArr = BiSq
  BiSq l ||| BiSq r = BiSq (r . l) \\\ l
  vArr (Str Bidiscrete) = BiSq id
  BiSq l === BiSq r = BiSq (l `o` r)
