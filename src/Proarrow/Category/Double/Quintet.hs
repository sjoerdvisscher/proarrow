{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Double.Quintet where

import Data.Function (($))

import Proarrow.Core (CAT, CategoryOf(..), Promonad (..), Profunctor(..), UN, Is, dimapDefault)
import Proarrow.Category.Double (Double (..))
import Proarrow.Category.Bicategory (Path(..), appendObj, Bicategory (..), type (+++), Fold, IsPath (..), Strictified (..), SPath (..), asObj)
import Proarrow.Category.Bicategory.Co (COK(..), Co(..), concatFoldCo, splitFoldCo)
import Proarrow.Object (obj, src, tgt)


type data QKK kk i j = QK (kk i j)
type instance UN QK (QK p) = p

type Q2 :: CAT (QKK kk i j)
data Q2 a b where
  Q2 :: a ~> b -> Q2 (QK a) (QK b)
instance CategoryOf (kk i j) => Profunctor (Q2 :: CAT (QKK kk i j)) where
  dimap = dimapDefault
  r \\ Q2 p = r \\ p
instance CategoryOf (kk i j) => Promonad (Q2 :: CAT (QKK kk i j)) where
  id = Q2 id
  Q2 f . Q2 g = Q2 (f . g)
instance CategoryOf (kk i j) => CategoryOf (QKK kk i j) where
  type (~>) = Q2
  type Ob (a :: QKK kk i j) = (Is QK a, Ob (UN QK a))

concatFoldQ
  :: forall {kk} {i} {j} {k} {ps :: Path (QKK kk) i j} (qs :: Path (QKK kk) j k)
   . (Bicategory kk, Ob qs, Ob0 kk i, Ob0 kk j, Ob0 kk k)
  => SPath ps -> UN QK (Fold ps) `O` UN QK (Fold qs) ~> UN QK (Fold (ps +++ qs))
concatFoldQ SNil = leftUnitor (obj @(UN QK (Fold qs)))
concatFoldQ (SCons (Q2 p) SNil) = case singPath @qs of
  SNil -> rightUnitor p
  SCons{} -> p `o` obj @(UN QK (Fold qs))
concatFoldQ (SCons @_ @ps1 (Q2 p) ps@SCons{})
  = (p `o` concatFoldQ @qs ps)
  . associator p (obj @(UN QK (Fold ps1))) (obj @(UN QK (Fold qs)))
  \\ asObj ps

splitFoldQ
  :: forall {kk} {i} {j} {k} {ps :: Path (QKK kk) i j} (qs :: Path (QKK kk) j k)
   . (Bicategory kk, Ob qs, Ob0 kk i, Ob0 kk j, Ob0 kk k)
  => SPath ps -> UN QK (Fold (ps +++ qs)) ~> UN QK (Fold ps) `O` UN QK (Fold qs)
splitFoldQ SNil = leftUnitorInv (obj @(UN QK (Fold qs)))
splitFoldQ (SCons (Q2 p) SNil) = case singPath @qs of
  SNil -> rightUnitorInv p
  SCons{} -> p `o` obj @(UN QK (Fold qs))
splitFoldQ (SCons @_ @ps1 (Q2 p) ps@SCons{})
  = associatorInv p (obj @(UN QK (Fold ps1))) (obj @(UN QK (Fold qs)))
  . (p `o` splitFoldQ @qs ps)
  \\ asObj ps

instance Bicategory kk => Bicategory (QKK kk) where
  type Ob0 (QKK kk) k = Ob0 kk k
  type I = QK I
  type O a b = QK (UN QK a `O` UN QK b)
  r \\\ Q2 f = r \\\ f
  Q2 f `o` Q2 g = Q2 (f `o` g)
  leftUnitor (Q2 p) = Q2 (leftUnitor p)
  leftUnitorInv (Q2 p) = Q2 (leftUnitorInv p)
  rightUnitor (Q2 p) = Q2 (rightUnitor p)
  rightUnitorInv (Q2 p) = Q2 (rightUnitorInv p)
  associator (Q2 p) (Q2 q) (Q2 r) = Q2 (associator p q r)
  associatorInv (Q2 p) (Q2 q) (Q2 r) = Q2 (associatorInv p q r)


type Quintet (ps :: Path (QKK kk) h j) = Sq (QKK kk) (COK kk) ps
type Quintet1 (p :: QKK kk h j) = Sq1 (QKK kk) (COK kk) p

-- | The quintet construction. Create a double category of squares @alpha :: ps +++ gs ~> fs +++ qs@ from a bicategory.
instance Bicategory kk => Double (QKK kk) (COK kk) where
  data Sq (QKK kk) (COK kk) ps qs fs gs where
    Q
      :: (IsPath ps, IsPath qs, IsPath fs, IsPath gs)
      => Sq1 (QKK kk) (COK kk) (Fold ps) (Fold qs) (Fold fs) (Fold gs)
      -> Sq (QKK kk) (COK kk) (ps :: Path (QKK kk) h j) (qs :: Path (QKK kk) i k) (fs :: Path (COK kk) h i) (gs :: Path (COK kk) j k)
  data Sq1 (QKK kk) (COK kk) p q f g where
    Q1
      :: (Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob p, Ob q, Ob f, Ob g)
      => UN QK p `O` UN CO g ~> UN CO f `O` UN QK q
      -> Sq1 (QKK kk) (COK kk) (p :: QKK kk h j) (q :: QKK kk i k) (f :: COK kk h i) (g :: COK kk j k)
  singleton = Q
  folded (Q sq) = sq
  r \\\\ Q (Q1 n) = r \\\ n
  object = Q $ Q1 (obj @I `o` obj @I)
  hArr (Str n) = Q (hArr1 n)
  hArr1 (Q2 n) = Q1 (leftUnitorInv (tgt n) . n . rightUnitor (src n)) \\ n
  vArr (Str n) = Q (vArr1 n)
  vArr1 (Co n) = Q1 (rightUnitorInv (tgt n) . n . leftUnitor (src n)) \\ n

  (|||) :: forall {h} {j} (ps :: Path (QKK kk) h j) qs rs fs gs hs is. Quintet ps qs fs gs -> Quintet qs rs hs is -> Quintet ps rs (fs +++ hs) (gs +++ is)
  Q (Q1 n) ||| Q (Q1 m) = appendObj @fs @hs $ appendObj @gs @is $
    let fs = obj @(UN CO (Fold fs))
        gs = obj @(UN CO (Fold gs))
        hs = obj @(UN CO (Fold hs))
        is = obj @(UN CO (Fold is))
        ps = obj @(UN QK (Fold ps))
        qs = obj @(UN QK (Fold qs))
        rs = obj @(UN QK (Fold rs))
    in Q $ Q1
      $ (concatFoldCo @hs (singPath @fs) `o` rs)
      . associatorInv fs hs rs
      . (fs `o` m)
      . associator fs qs is
      . (n `o` is)
      . associatorInv ps gs is
      . (ps `o` splitFoldCo @is (singPath @gs))

  (===) :: forall {h} {i} (ps :: Path (QKK kk) h i) qs rs ss fs gs hs. Quintet ps qs fs gs -> Quintet rs ss gs hs -> Quintet (ps +++ rs) (qs +++ ss) fs hs
  Q (Q1 n) === Q (Q1 m) = appendObj @ps @rs $ appendObj @qs @ss $
    let fs = obj @(UN CO (Fold fs))
        gs = obj @(UN CO (Fold gs))
        hs = obj @(UN CO (Fold hs))
        ps = obj @(UN QK (Fold ps))
        qs = obj @(UN QK (Fold qs))
        rs = obj @(UN QK (Fold rs))
        ss = obj @(UN QK (Fold ss))
    in Q $ Q1
      $ (fs `o` concatFoldQ @ss (singPath @qs))
      . associator fs qs ss
      . (n `o` ss)
      . associatorInv ps gs ss
      . (ps `o` m)
      . associator ps rs hs
      . (splitFoldQ @rs (singPath @ps) `o` hs)

-- Quintet is not an Equipment