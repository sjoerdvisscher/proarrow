{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Double.Prof where

import Data.Function (($))

import Proarrow.Category.Bicategory (Path(..))
import Proarrow.Core (CategoryOf(..), Profunctor(..), Promonad (..), UN, Is)
import Proarrow.Category.Bicategory.Prof (ProfK(..), PSplit(..), ProfList(..), Biprof(..), withAppendPSplit, pappend, ProfC, ProfCorepC)
import Proarrow.Category.Double (DOUBLE, Double (..), Equipment(..), TmpOb, Companion, Conjoint)
import Proarrow.Profunctor.Corepresentable (Corepresentable(..))
import Proarrow.Category.Bicategory.Cat (FunK(..), FList, ApplyAll, Cat (..), withAppendFList)
import Proarrow.Profunctor.Costar (Costar(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Functor (Functor(..))




-- type ProfSq :: DOUBLE (ProfK clh) (ProfK clv)
-- data ProfSq ps qs fs gs where
--   ProfSq
--     :: forall {h} {i} {j} {k} {clh} {clv} ps qs fs gs
--      . (CategoryOf h, CategoryOf i, CategoryOf j, CategoryOf k, PSplit ps, PSplit qs, PSplit fs, PSplit gs)
--     => ProfList clh ps :~> CostarRep (ProfList clv fs) :.: ProfList clh qs :.: StarRep (ProfList clv gs)
--     -> ProfSq (ps :: Path (ProfK clh) h i) (qs :: Path (ProfK clh) j k) (fs :: Path (ProfK clv) h j) (gs :: Path (ProfK clv) i k)

type ProfSq :: DOUBLE (ProfK clh) FunK
data ProfSq ps qs fs gs where
  ProfSq
    :: forall {h} {i} {j} {k} {clh} ps qs fs gs
     . (CategoryOf h, CategoryOf i, CategoryOf j, CategoryOf k, PSplit ps, PSplit qs, FList fs, FList gs)
    => (forall (a :: h) (b :: j). ProfList clh ps a b -> ProfList clh qs (ApplyAll fs a) (ApplyAll gs b))
    -> ProfSq (ps :: Path (ProfK clh) h j) (qs :: Path (ProfK clh) i k) (fs :: Path FunK h i) (gs :: Path FunK j k)

instance Double (ProfK ProfC) FunK where
  type Sq (ProfK ProfC) FunK = ProfSq
  object = ProfSq id
  hArr (Biprof f) = ProfSq f
  vArr (Cat n) = ProfSq \(ProfNil f) -> ProfNil (n f)
  ProfSq @_ @_ @fs @gs n ||| ProfSq @_ @_ @hs @is m = withAppendFList @gs @is $ withAppendFList @fs @hs $ ProfSq (m . n)
  ProfSq @ps @qs n === ProfSq @rs @ss m = withAppendPSplit @ps @rs $ withAppendPSplit @qs @ss $ ProfSq $ psplit (\ps rs -> pappend (n ps) (m rs))

instance Equipment (ProfK ProfC) FunK where
  type Companion (ProfK ProfC) FunK f = PK (Costar (UN FK f))
  type Conjoint (ProfK ProfC) FunK f = PK (Star (UN FK f))
  fromRight = ProfSq \(ProfNil f) -> ProfCons (Costar (map f)) (ProfNil id) \\ f
  toLeft = ProfSq \(ProfCons (Costar f) (ProfNil g)) -> ProfNil (g . f)
  toRight = ProfSq \(ProfNil f) -> ProfCons (Star (map f)) (ProfNil id) \\ f
  fromLeft = ProfSq \(ProfCons (Star f) (ProfNil g)) -> ProfNil (map g . f)

-- | The double category of profunctors.
-- instance Double (ProfK clh) (ProfK clv) where
--   type Sq (ProfK clh) (ProfK clv) = ProfSq
--   -- object = ProfSq \(ProfNil f :.: ProfNil g) -> ProfNil f :.: ProfNil g
--   -- hArr (Biprof n) = ProfSq \(ps :.: ProfNil f) -> ProfNil id :.: rmap f (n ps) \\ ps
--   -- ProfSq @_ @_ @fs @gs n ||| ProfSq @_ @_ @hs @is m = withAppendPSplit @gs @is $ withAppendPSplit @fs @hs $ ProfSq \(ps :.: gis) ->
--   --   psplit
--   --     (\gs is -> case n (ps :.: gs) of
--   --       fs :.: qs -> case m (qs :.: is) of
--   --         hs :.: rs -> pappend fs hs :.: rs)
--   --     gis
--   -- vArr (Biprof n) = ProfSq \(ProfNil f :.: ps) -> lmap f (n ps) :.: ProfNil id \\ ps
--   -- ProfSq @ps @qs n === ProfSq @rs @ss m = withAppendPSplit @ps @rs $ withAppendPSplit @qs @ss $ ProfSq \(prs :.: hs) ->
--   --   psplit
--   --     (\ps rs -> case m (rs :.: hs) of
--   --       gs :.: ss -> case n (ps :.: gs) of
--   --         fs :.: qs -> fs :.: pappend qs ss)
--   --   prs

-- type StarRep :: PRO j k -> PRO k j
-- newtype StarRep p a b = StarRep (a ~> (p %% b))
-- instance Profunctor p => Profunctor (StarRep p)
-- type CostarRep :: PRO k j -> PRO k j
-- newtype CostarRep p a b = CostarRep ((p %% a) ~> b)
-- instance Profunctor p => Profunctor (CostarRep p)

type instance TmpOb (ProfK ProfC) f = (Is PK f)
type instance TmpOb (ProfK ProfCorepC) f = (Is PK f, Corepresentable (UN PK f))
type instance TmpOb FunK f = (Is FK f, Functor (UN FK f))

-- instance Equipment (ProfK ProfC) (ProfK ProfCorepC) where
--   type Companion (ProfK ProfC) (ProfK ProfCorepC) p = PK (CostarRep (UN PK p))
--   type Conjoint (ProfK ProfC) (ProfK ProfCorepC) p = PK (StarRep (UN PK p))
--   fromRight = ProfSq \(ProfNil f) -> CostarRep id :.: ProfCons (CostarRep _) (ProfNil _) :.: StarRep _
--   -- toLeft = ProfSq \(ProfCons (StarRep f) (ProfNil g) :.: ProfNil h) -> ProfCons (tabulate f) (ProfNil g) :.: ProfNil h \\ g
--   -- toRight = ProfSq \(ProfNil f :.: ProfNil g) -> ProfCons (tabulate id) (ProfNil id) :.: ProfCons (CostarRep _) (ProfNil g)
--   fromLeft = ProfSq \(ProfCons (StarRep f) (ProfNil g)) -> CostarRep id :.: ProfNil id :.: StarRep (corepMap g . f)
