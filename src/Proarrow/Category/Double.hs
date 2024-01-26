{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Double where

import Data.Kind (Type)

import Proarrow.Core (CategoryOf(..), CAT, UN)
import Proarrow.Category.Bicategory (Path(..), type (+++), Bicategory(..), Fold, Strictified (..), appendObj, IsPath (..))
import Proarrow.Object (Obj)
import Proarrow.Category.Bicategory.Op (OPK(OP), Op (..))
import Proarrow.Category.Bicategory.Co (COK(CO), Co (..), splitFoldCo, concatFoldCo)
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
class (Bicategory hk, Bicategory vk) => Double (sq :: SQ hk vk) where
  data Sq1 sq :: SQ1 hk vk
  singleton :: (DOb sq h, DOb sq i, DOb sq j, DOb sq k, Ob (p :: hk h j), Ob (q :: hk i k), Ob (f :: vk h i), Ob (g :: vk j k)) =>
    Sq1 sq p q f g -> sq (p ::: Nil) (q ::: Nil) (f ::: Nil) (g ::: Nil)
  folded :: (DOb sq h, DOb sq i, DOb sq j, DOb sq k, Ob (ps :: Path hk h j), Ob (qs :: Path hk i k), Ob (fs :: Path vk h i), Ob (gs :: Path vk j k)) =>
    sq ps qs fs gs -> Sq1 sq (Fold ps) (Fold qs) (Fold fs) (Fold gs)
  -- | The empty square for an object.
  object :: DOb sq k => sq (Nil :: Path hk k k) Nil Nil Nil
  -- | Make a square from a horizontal arrow
  hArr :: (DOb sq j, DOb sq k) => (ps :: Path hk j k) ~> qs -> sq ps qs Nil Nil
  hArr1 :: (DOb sq j, DOb sq k) => (p :: hk j k) ~> q -> Sq1 sq p q I I
  -- | Horizontal composition
  (|||) :: sq ps qs fs gs -> sq qs rs hs is -> sq ps rs (fs +++ hs) (gs +++ is)
  -- | Make a square from a vertical arrow (in the opposite direction to match the quintet construction)
  vArr :: (DOb sq j, DOb sq k) => (fs :: Path vk j k) ~> gs -> sq Nil Nil fs gs
  vArr1 :: (DOb sq j, DOb sq k) => (f :: vk j k) ~> g -> Sq1 sq I I f g
  -- | Vertical composition
  (===) :: sq ps qs fs gs -> sq rs ss gs hs -> sq (ps +++ rs) (qs +++ ss) fs hs
  (\\\\) :: ((DOb sq h, DOb sq i, DOb sq j, DOb sq k, Ob ps, Ob qs, Ob fs, Ob gs) => r) -> sq (ps :: Path hk h j) (qs :: Path hk i k) fs gs -> r

type DOb (sq :: SQ hk vk) k = (Ob0 hk k, Ob0 vk k)

class Double sq => Equipment (sq :: SQ hk vk) where
  type Companion sq (f :: vk j k) :: hk j k
  type Conjoint sq (f :: vk j k) :: hk k j
  fromRight :: (DOb sq j, DOb sq k, Ob (f :: vk j k)) => sq Nil (Companion sq f ::: Nil) Nil (f ::: Nil)
  toLeft :: (DOb sq j, DOb sq k, Ob (f :: vk j k)) => sq (Companion sq f ::: Nil) Nil (f ::: Nil) Nil
  toRight :: (DOb sq j, DOb sq k, Ob (f :: vk j k)) => sq Nil (Conjoint sq f ::: Nil) (f ::: Nil) Nil
  fromLeft :: (DOb sq j, DOb sq k, Ob (f :: vk j k)) => sq (Conjoint sq f ::: Nil) Nil Nil (f ::: Nil)
  withComOb :: (DOb sq j, DOb sq k, Ob (f :: vk j k)) => Obj f -> (Ob (Companion sq f) => r) -> r
  withConOb :: (DOb sq j, DOb sq k, Ob (f :: vk j k)) => Obj f -> (Ob (Conjoint sq f) => r) -> r


-- type UnOp ps = UN OP (Fold ps)
-- type UnCo fs = UN CO (Fold fs)
-- type CoSq1 :: forall hk -> forall vk -> SQ (OPK hk) (COK vk)

-- type CoSq :: forall {hk} {vk}. SQ hk vk -> SQ (OPK hk) (COK vk)
-- data CoSq sq ps qs fs gs where
--   CoSq :: (Ob ps, Ob qs, Ob fs, Ob gs) => Sq1 (CoSq sq) (Fold ps) (Fold qs) (Fold fs) (Fold gs)
--     -> CoSq (sq :: SQ hk vk) (ps :: Path (OPK hk) h j) (qs :: Path (OPK hk) i k)  (fs :: Path (COK vk) h i) (gs :: Path (COK vk) j k)

-- -- mkCoSq :: Double hk vk => (Ob ps, Ob qs, Ob fs, Ob gs) => sq (UnOp ps) (UnOp qs) (UnCo gs) (UnCo fs) -> Cosq ps qs fs gs
-- -- mkCoSq sq = CoSq sq \\\\ sq

-- instance Double sq => Double (CoSq sq) where
--   data Sq1 (CoSq sq) p q f g where
--     CoSq1 :: Sq1 sq (UN OP p) (UN OP q) (UN CO g) (UN CO f) -> CoSq1 (CoSq sq) p q f g
--   singleton = CoSq
--   folded (CoSq sq) = sq
--   object = CoSq $ CoSq1 $ folded object
--   hArr (Str (Op f)) = CoSq $ CoSq1 $ hArr1 f
--   hArr1 (Op f) = CoSq1 $ hArr1 f
--   vArr :: forall {i} {j} fs gs. (DOb sq i, DOb sq j) => (fs :: Path (COK vk) i j) ~> gs -> Cosq Nil Nil fs gs
--   vArr (Str (Co f)) = CoSq $ CoSq1 $ folded (vArr (Str @(UN CO (Fold gs) ::: Nil) @(UN CO (Fold fs) ::: Nil) f))
--   l@(CoSq @_ @_ @_ @_ @fs @gs (CoSq1 f)) ||| r@(CoSq @_ @_ @_ @_ @hs @is (CoSq1 g)) =
--     (appendObj @fs @hs $ appendObj @gs @is $ CoSq $ CoSq1 $ folded $
--        Str (splitFoldCo @is (singPath @gs))
--        === singleton f ||| singleton g ===
--         Str (concatFoldCo @hs (singPath @fs))
--     ) \\\\ l \\\\ r
--   l@(CoSq @_ @ps @qs (CoSq1 f)) === r@(CoSq @_ @rs @ss (CoSq1 g)) =
--     (appendObj @ps @rs $ appendObj @qs @ss $ CoSq $ CoSq1 $ folded (singleton g === singleton f)) \\\\ l \\\\ r
--   r \\\\ CoSq (CoSq1 sq) = r \\\\ singleton sq

-- -- instance Equipment hk vk => Equipment (OPK hk) (COK vk) where
-- --   type Companion (OPK hk) (COK vk) f = OP (Conjoint sq (UN CO f))
-- --   type Conjoint (OPK hk) (COK vk) f = OP (Companion sq (UN CO f))
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