{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Double.ProfFun where

import Data.Function (($))

import Proarrow.Core (CategoryOf(..), Promonad (..), (\\))
import Proarrow.Category.Double (DOUBLE, Double (..), Equipment (..))
import Proarrow.Category.Bicategory (Path(..), isPathAppend)
import Proarrow.Category.Bicategory.Cat (ApplyAll, Cat (..), withAppendFList)
import Proarrow.Category.Bicategory.Prof (ProfK(..), ProfList (..), Biprof (..), psplit, pappend, ProfC)
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Functor (map)

type ProfSq :: DOUBLE (ProfK clh) (->)
data ProfSq ps qs fs gs where
  ProfSq
    :: forall {h} {i} {j} {k} {clh} ps qs fs gs
     . (CategoryOf h, CategoryOf i, CategoryOf j, CategoryOf k, Ob ps, Ob qs, Ob fs, Ob gs)
    => (forall (a :: h) (b :: j). ProfList clh ps a b -> ProfList clh qs (ApplyAll fs a) (ApplyAll gs b))
    -> ProfSq (ps :: Path (ProfK clh) h j) (qs :: Path (ProfK clh) i k) (fs :: Path (->) h i) (gs :: Path (->) j k)

instance Double (ProfK clh) (->) where
  type Sq (ProfK clh) (->) = ProfSq
  object = ProfSq id
  hArr (Biprof f) = ProfSq f
  vArr (Cat n) = ProfSq \(ProfNil f) -> ProfNil (n f)
  ProfSq @_ @_ @fs @gs n ||| ProfSq @_ @_ @hs @is m = withAppendFList @gs @is $ withAppendFList @fs @hs $ ProfSq (m . n)
  ProfSq @ps @qs n === ProfSq @rs @ss m = isPathAppend @ps @rs $ isPathAppend @qs @ss $ ProfSq $ psplit (\ps rs -> pappend (n ps) (m rs))

instance Equipment (ProfK ProfC) (->) where
  type Companion (ProfK ProfC) (->) f = PK (Costar f)
  type Conjoint (ProfK ProfC) (->) f = PK (Star f)
  fromRight = ProfSq \(ProfNil f) -> ProfCons (Costar (map f)) (ProfNil id) \\ f
  toLeft = ProfSq \(ProfCons (Costar f) (ProfNil g)) -> ProfNil (g . f)
  toRight = ProfSq \(ProfNil f) -> ProfCons (Star (map f)) (ProfNil id) \\ f
  fromLeft = ProfSq \(ProfCons (Star f) (ProfNil g)) -> ProfNil (map g . f)