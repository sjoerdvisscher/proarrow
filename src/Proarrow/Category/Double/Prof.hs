{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Double.Prof where

import Data.Function (($))

import Proarrow.Category.Bicategory (Path(..))
import Proarrow.Core (CategoryOf(..), Profunctor(..), (:~>), Promonad (..), lmap, rmap)
import Proarrow.Category.Bicategory.Prof (ProfK(..), PSplit(..), ProfList(..), Biprof(..), withAppendPSplit, pappend)
import Proarrow.Category.Double (DOUBLE, Double (..))
import Proarrow.Profunctor.Composition ((:.:) (..))




type ProfSq :: DOUBLE ProfK ProfK
data ProfSq ps qs fs gs where
  ProfSq
    :: forall {h} {i} {j} {k} ps qs fs gs
     . (CategoryOf h, CategoryOf i, CategoryOf j, CategoryOf k, PSplit ps, PSplit qs, PSplit fs, PSplit gs)
    => ProfList ps :.: ProfList gs :~> ProfList fs :.: ProfList qs
    -> ProfSq (ps :: Path ProfK h i) (qs :: Path ProfK j k) fs gs


-- | The double category of profunctors.
instance Double ProfK ProfK where
  type Sq ProfK ProfK = ProfSq
  object = ProfSq id
  hArr (Biprof n) = ProfSq \(ps :.: ProfNil f) -> ProfNil id :.: rmap f (n ps) \\ ps
  ProfSq @_ @_ @fs @gs n ||| ProfSq @_ @_ @hs @is m = withAppendPSplit @gs @is $ withAppendPSplit @fs @hs $ ProfSq \(ps :.: gis) ->
    psplit
      (\gs is -> case n (ps :.: gs) of
        fs :.: qs -> case m (qs :.: is) of
          hs :.: rs -> pappend fs hs :.: rs)
      gis
  vArr (Biprof n) = ProfSq \(ProfNil f :.: ps) -> lmap f (n ps) :.: ProfNil id \\ ps
  ProfSq @ps @qs n === ProfSq @rs @ss m = withAppendPSplit @ps @rs $ withAppendPSplit @qs @ss $ ProfSq \(prs :.: hs) ->
    psplit
      (\ps rs -> case m (rs :.: hs) of
        gs :.: ss -> case n (ps :.: gs) of
          fs :.: qs -> fs :.: pappend qs ss)
    prs
