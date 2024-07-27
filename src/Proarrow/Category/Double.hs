{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Double where

import Data.Kind (Type)

import Proarrow.Category.Bicategory
  ( Bicategory (..)
  , Fold
  , IsPath (..)
  , Path (..)
  , Strictified (..)
  , appendObj
  , type (+++)
  )
import Proarrow.Category.Bicategory.Co (COK (CO), Co (..), concatFoldCo, splitFoldCo)
import Proarrow.Category.Bicategory.Op (OPK (OP), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), UN)
import Proarrow.Object (Obj)
import Prelude (($))

infixl 6 |||
infixl 5 ===

-- |
-- The kind of a square @p q f g@.
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--g--k
type SQ1 (hk :: CAT c) (vk :: CAT c) = forall {h} {i} {j} {k}. hk h j -> hk i k -> vk h i -> vk j k -> Type

type SQ (hk :: CAT c) (vk :: CAT c) = SQ1 (Path hk) (Path vk)

-- | Double categories, strictified in both directions.
class (Bicategory hk, Bicategory vk) => Double hk vk where
  data Sq hk vk :: SQ hk vk
  data Sq1 hk vk :: SQ1 hk vk
  singleton
    :: ( DOb hk vk h
       , DOb hk vk i
       , DOb hk vk j
       , DOb hk vk k
       , Ob (p :: hk h j)
       , Ob (q :: hk i k)
       , Ob (f :: vk h i)
       , Ob (g :: vk j k)
       )
    => Sq1 hk vk p q f g -> Sq hk vk (p ::: Nil) (q ::: Nil) (f ::: Nil) (g ::: Nil)
  folded
    :: ( DOb hk vk h
       , DOb hk vk i
       , DOb hk vk j
       , DOb hk vk k
       , Ob (ps :: Path hk h j)
       , Ob (qs :: Path hk i k)
       , Ob (fs :: Path vk h i)
       , Ob (gs :: Path vk j k)
       )
    => Sq hk vk ps qs fs gs -> Sq1 hk vk (Fold ps) (Fold qs) (Fold fs) (Fold gs)

  -- | The empty square for an object.
  object :: (DOb hk vk k) => Sq hk vk (Nil :: Path hk k k) Nil Nil Nil

  -- | Make a square from a horizontal arrow
  hArr :: (DOb hk vk j, DOb hk vk k) => (ps :: Path hk j k) ~> qs -> Sq hk vk ps qs Nil Nil

  hArr1 :: (DOb hk vk j, DOb hk vk k) => (p :: hk j k) ~> q -> Sq1 hk vk p q I I

  -- | Horizontal composition
  (|||) :: Sq hk vk ps qs fs gs -> Sq hk vk qs rs hs is -> Sq hk vk ps rs (fs +++ hs) (gs +++ is)

  -- | Make a square from a vertical arrow (in the opposite direction to match the quintet construction)
  vArr :: (DOb hk vk j, DOb hk vk k) => (fs :: Path vk j k) ~> gs -> Sq hk vk Nil Nil fs gs

  vArr1 :: (DOb hk vk j, DOb hk vk k) => (f :: vk j k) ~> g -> Sq1 hk vk I I f g

  -- | Vertical composition
  (===) :: Sq hk vk ps qs fs gs -> Sq hk vk rs ss gs hs -> Sq hk vk (ps +++ rs) (qs +++ ss) fs hs

  (\\\\)
    :: ((DOb hk vk h, DOb hk vk i, DOb hk vk j, DOb hk vk k, Ob ps, Ob qs, Ob fs, Ob gs) => r)
    -> Sq hk vk (ps :: Path hk h j) (qs :: Path hk i k) fs gs
    -> r

type DOb hk vk k = (Ob0 hk k, Ob0 vk k)

class (Double hk vk) => Equipment hk vk where
  type Companion hk vk (f :: vk j k) :: hk j k
  type Conjoint hk vk (f :: vk j k) :: hk k j
  fromRight :: (DOb hk vk j, DOb hk vk k, Ob (f :: vk j k)) => Sq hk vk Nil (Companion hk vk f ::: Nil) Nil (f ::: Nil)
  toLeft :: (DOb hk vk j, DOb hk vk k, Ob (f :: vk j k)) => Sq hk vk (Companion hk vk f ::: Nil) Nil (f ::: Nil) Nil
  toRight :: (DOb hk vk j, DOb hk vk k, Ob (f :: vk j k)) => Sq hk vk Nil (Conjoint hk vk f ::: Nil) (f ::: Nil) Nil
  fromLeft :: (DOb hk vk j, DOb hk vk k, Ob (f :: vk j k)) => Sq hk vk (Conjoint hk vk f ::: Nil) Nil Nil (f ::: Nil)
  withComOb :: (DOb hk vk j, DOb hk vk k, Ob (f :: vk j k)) => Obj f -> ((Ob (Companion hk vk f)) => r) -> r
  withConOb :: (DOb hk vk j, DOb hk vk k, Ob (f :: vk j k)) => Obj f -> ((Ob (Conjoint hk vk f)) => r) -> r

type UnOp ps = UN OP (Fold ps)
type UnCo fs = UN CO (Fold fs)

-- type CoSq1 :: forall hk -> forall vk -> SQ (OPK hk) (COK vk)

-- type CoSq :: forall {hk} {vk}. SQ hk vk -> SQ (OPK hk) (COK vk)
-- data CoSq hk vk ps qs fs gs where
--   CoSq :: (Ob ps, Ob qs, Ob fs, Ob gs) => Sq1 (CoSq hk vk) (Fold ps) (Fold qs) (Fold fs) (Fold gs)
--     -> CoSq (Sq hk vk :: SQ hk vk) (ps :: Path (OPK hk) h j) (qs :: Path (OPK hk) i k)  (fs :: Path (COK vk) h i) (gs :: Path (COK vk) j k)

-- mkCoSq :: Double hk vk => (Ob ps, Ob qs, Ob fs, Ob gs) => Sq hk vk (UnOp ps) (UnOp qs) (UnCo gs) (UnCo fs) -> Cosq ps qs fs gs
-- mkCoSq hk vk = CoSq hk vk \\\\ Sq hk vk

type CoSq (ps :: Path (OPK hk) h j) (qs :: Path (OPK hk) i k) (fs :: Path (COK vk) h i) (gs :: Path (COK vk) j k) =
  Sq (OPK hk) (COK vk) ps qs fs gs

instance (Double hk vk) => Double (OPK hk) (COK vk) where
  data Sq (OPK hk) (COK vk) ps qs fs gs where
    CoSq
      :: forall {hk} {vk} {h} {i} {j} {k} ps qs fs gs
       . (Ob ps, Ob qs, Ob fs, Ob gs)
      => Sq1 (OPK hk) (COK vk) (Fold ps) (Fold qs) (Fold fs) (Fold gs)
      -> Sq
          (OPK hk)
          (COK vk)
          (ps :: Path (OPK hk) h j)
          (qs :: Path (OPK hk) i k)
          (fs :: Path (COK vk) h i)
          (gs :: Path (COK vk) j k)
  data Sq1 (OPK hk) (COK vk) p q f g where
    CoSq1 :: Sq1 hk vk (UN OP p) (UN OP q) (UN CO g) (UN CO f) -> Sq1 (OPK hk) (COK vk) p q f g
  singleton = CoSq
  folded (CoSq sq) = sq
  object = CoSq $ CoSq1 $ folded object
  hArr (Str fs) = CoSq $ hArr1 fs
  hArr1 (Op f) = CoSq1 $ hArr1 f
  vArr (Str fs) = CoSq $ vArr1 fs
  vArr1 (Co f) = CoSq1 $ vArr1 f

-- l@(CoSq @_ @_ @fs @gs (CoSq1 f)) ||| r@(CoSq @_ @_ @hs @is (CoSq1 g)) =
--   (appendObj @fs @hs $ appendObj @gs @is $ CoSq $ CoSq1 $
--     folded $
--       Str (splitFoldCo @is (singPath @gs))
--       === singleton f ||| singleton g ===
--         Str (concatFoldCo @hs (singPath @fs))
--   ) \\\\ l \\\\ r
-- l@(CoSq @ps @qs (CoSq1 f)) === r@(CoSq @rs @ss (CoSq1 g)) =
--   (appendObj @ps @rs $ appendObj @qs @ss $ CoSq $ CoSq1 $ folded (singleton g === singleton f)) \\\\ l \\\\ r
-- r \\\\ CoSq (CoSq1 sq) = r \\\\ singleton sq

-- -- instance Equipment hk vk => Equipment (OPK hk) (COK vk) where
-- --   type Companion (OPK hk) (COK vk) f = OP (Conjoint hk vk (UN CO f))
-- --   type Conjoint (OPK hk) (COK vk) f = OP (Companion hk vk (UN CO f))
-- --   fromRight :: forall j k (f :: COK vk j k). (DOb (OPK hk) (COK vk) j, DOb (OPK hk) (COK vk) k, Ob f)
-- --     => Sq (OPK hk) (COK vk) Nil (Companion (OPK hk) (COK vk) f ::: Nil) Nil (f ::: Nil)
-- --   fromRight = withConOb @hk @vk @j @k @(UN CO f) (obj @(UN CO f)) $ mkCoSq _
-- --   toLeft :: forall j k (f :: COK vk j k). (DOb (OPK hk) (COK vk) j, DOb (OPK hk) (COK vk) k, Ob (COK vk) f)
-- --     => Sq (OPK hk) (COK vk) (Companion (OPK hk) (COK vk) f ::: Nil) Nil (f ::: Nil) Nil
-- --   toLeft = withConOb @hk @vk @j @k @(UN CO f) (obj @(UN CO f)) $ mkCoSq fromLeft
-- --   toRight :: forall j k (f :: COK vk j k). (DOb (OPK hk) (COK vk) j, DOb (OPK hk) (COK vk) k, Ob (COK vk) f)
-- --     => Sq (OPK hk) (COK vk) Nil (Conjoint (OPK hk) (COK vk) f ::: Nil) (f ::: Nil) Nil
-- --   toRight = withComOb @hk @vk @j @k @(UN CO f) (obj @(UN CO f)) $ mkCoSq fromRight
-- --   fromLeft :: forall j k (f :: COK vk j k). (DOb (OPK hk) (COK vk) j, DOb (OPK hk) (COK vk) k, Ob (COK vk) f)
-- --     => Sq (OPK hk) (COK vk) (Conjoint (OPK hk) (COK vk) f ::: Nil) Nil Nil (f ::: Nil)
-- --   fromLeft = withComOb @hk @vk @j @k @(UN CO f) (obj @(UN CO f)) $ mkCoSq toLeft
-- --   -- withComOb (Co f) = withConOb @hk @vk f
