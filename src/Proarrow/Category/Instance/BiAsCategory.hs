{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.BiAsCategory where

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Functor (FunctorForRep (..))

newtype BI (kk :: CAT s) = B s
type instance UN B (B s) = s

type Bi :: CAT (BI kk)
data Bi a b where
  Bi :: forall {kk} {j} {k} p. (Ob (p :: kk j k), Ob0 kk j, Ob0 kk k) => Bi (B j :: BI kk) (B k)

-- | The category of 0-cells and 1-cells of a bicategory, forgetting 2-cells.
instance (Bicategory kk) => CategoryOf (BI kk) where
  type (~>) = Bi
  type Ob @(BI kk) c = (Is B c, Ob0 kk (UN B c))

instance (Bicategory kk) => Promonad (Bi :: CAT (BI kk)) where
  id @(B k) = Bi @(I :: kk k k)
  Bi @p . Bi @q = withOb2 @kk @p @q (Bi @(p `O` q))

instance (Bicategory kk) => Profunctor (Bi :: CAT (BI kk)) where
  dimap = dimapDefault
  r \\ Bi = r

data family Comp :: (kk j k, kk i j) +-> kk i k
instance (Bicategory kk, Ob0 kk i, Ob0 kk j, Ob0 kk k) => FunctorForRep (Comp :: (kk j k, kk i j) +-> kk i k) where
  type Comp @ '(f, g) = (f `O` g)
  fmap (n :**: m) = n `o` m \\ n \\ m