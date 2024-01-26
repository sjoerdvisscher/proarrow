{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Double.Quintet where

import Data.Function (($))

import Proarrow.Core (CategoryOf(..), Promonad (..), Profunctor(..), UN)
import Proarrow.Category.Double (SQ, Double (..))
import Proarrow.Category.Bicategory (Path(..), appendObj, Bicategory (..), type (+++), Fold, concatFold, splitFold, IsPath (..), Strictified (..))
import Proarrow.Category.Bicategory.Co (COK(..), Co(..), concatFoldCo, splitFoldCo)
import Proarrow.Object (obj, src, tgt)


type Quintet :: SQ kk (COK kk)
data Quintet ps qs fs gs where
  Q
    :: (IsPath ps, IsPath qs, IsPath fs, IsPath gs)
    => Sq1 Quintet (Fold ps) (Fold qs) (Fold fs) (Fold gs)
    -> Quintet (ps :: Path kk h j) (qs :: Path kk i k) (fs :: Path (COK kk) h i) (gs :: Path (COK kk) j k)

-- | The quintet construction. Create a double category of squares @alpha :: ps +++ gs ~> fs +++ qs@ from a bicategory.
instance Bicategory kk => Double (Quintet :: SQ kk (COK kk)) where
  data Sq1 Quintet p q f g where
    Q1
      :: (Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob p, Ob q, Ob f, Ob g)
      => p `O` UN CO g ~> UN CO f `O` q
      -> Sq1 Quintet (p :: kk h j) (q ::  kk i k) (f :: COK kk h i) (g :: COK kk j k)
  singleton = Q
  folded (Q sq) = sq
  r \\\\ Q (Q1 n) = r \\\ n
  object = Q $ Q1 (obj @I `o` obj @I)
  hArr (Str n) = Q (hArr1 n)
  hArr1 n = Q1 (leftUnitorInv (tgt n) . n . rightUnitor (src n)) \\ n
  vArr (Str n) = Q (vArr1 n)
  vArr1 (Co n) = Q1 (rightUnitorInv (tgt n) . n . leftUnitor (src n)) \\ n

  (|||) :: forall {h} {j} (ps :: Path kk h j) qs rs fs gs hs is. Quintet ps qs fs gs -> Quintet qs rs hs is -> Quintet ps rs (fs +++ hs) (gs +++ is)
  Q (Q1 n) ||| Q (Q1 m) = appendObj @fs @hs $ appendObj @gs @is $
    let fs = obj @(UN CO (Fold fs))
        gs = obj @(UN CO (Fold gs))
        hs = obj @(UN CO (Fold hs))
        is = obj @(UN CO (Fold is))
        ps = obj @(Fold ps)
        qs = obj @(Fold qs)
        rs = obj @(Fold rs)
    in Q $ Q1
      $ (concatFoldCo @hs (singPath @fs) `o` rs)
      . associatorInv fs hs rs
      . (fs `o` m)
      . associator fs qs is
      . (n `o` is)
      . associatorInv ps gs is
      . (ps `o` splitFoldCo @is (singPath @gs))

  (===) :: forall {h} {i} (ps :: Path kk h i) qs rs ss fs gs hs. Quintet ps qs fs gs -> Quintet rs ss gs hs -> Quintet (ps +++ rs) (qs +++ ss) fs hs
  Q (Q1 n) === Q (Q1 m) = appendObj @ps @rs $ appendObj @qs @ss $
    let fs = obj @(UN CO (Fold fs))
        gs = obj @(UN CO (Fold gs))
        hs = obj @(UN CO (Fold hs))
        ps = obj @(Fold ps)
        qs = obj @(Fold qs)
        rs = obj @(Fold rs)
        ss = obj @(Fold ss)
    in Q $ Q1
      $ (fs `o` concatFold @qs @ss)
      . associator fs qs ss
      . (n `o` ss)
      . associatorInv ps gs ss
      . (ps `o` m)
      . associator ps rs hs
      . (splitFold @ps @rs `o` hs)

-- Quintet is not an Equipment