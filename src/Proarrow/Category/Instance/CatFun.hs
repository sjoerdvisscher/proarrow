{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.CatFun where

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.Prof
import Proarrow.Category.Enriched (EnrichedProfunctor (..))
import Proarrow.Category.Instance.BiAsCategory (BI (..), Bi (..), Comp)
import Proarrow.Category.Instance.CatProf (Swap)
import Proarrow.Category.Instance.Coproduct (COPRODUCT, Codiag, Lft, Rgt, (:++:))
import Proarrow.Category.Instance.Product (Diag, Fst, Snd, (:**:) (..))
import Proarrow.Category.Instance.Prof qualified as F
import Proarrow.Category.Instance.Sub qualified as F
import Proarrow.Category.Instance.Zero (Absurd, VOID)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  )
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:))
import Proarrow.Profunctor.Constant (Constant)
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), withObRep)

instance HasTerminalObject (BI FUNK) where
  type TerminalObject = B ()
  terminate = Bi @(FUN (Rep (Constant '())))

instance HasInitialObject (BI FUNK) where
  type InitialObject = B VOID
  initiate = Bi @(FUN (Rep Absurd))

instance HasBinaryProducts (BI FUNK) where
  type B l && B r = B (l, r)
  withObProd r = r
  fst = Bi @(FUN (Rep Fst))
  snd = Bi @(FUN (Rep Snd))
  Bi @(FUN p) &&& Bi @(FUN q) = Bi @(FUN ((p :**: q) :.: Rep Diag))

instance HasBinaryCoproducts (BI FUNK) where
  type B l || B r = B (COPRODUCT l r)
  withObCoprod r = r
  lft = Bi @(FUN (Rep Lft))
  rgt = Bi @(FUN (Rep Rgt))
  Bi @(FUN p) ||| Bi @(FUN q) = Bi @(FUN (Rep Codiag :.: (p :++: q)))

instance M.MonoidalProfunctor (Bi :: CAT (BI FUNK)) where
  par0 = id
  Bi @(FUN f) `par` Bi @(FUN g) = Bi @(FUN (f :**: g))

instance M.Monoidal (BI FUNK) where
  type Unit = B ()
  type B j ** B k = B (j, k)
  withOb2 r = r
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance M.SymMonoidal (BI FUNK) where
  swap = Bi @(FUN (Rep Swap))

data family CurryH :: (i, j) +-> k -> i -> j +-> k
instance (Representable f, Ob (a :: i), CategoryOf i, CategoryOf j) => FunctorForRep (CurryH f a :: j +-> k) where
  type CurryH f a @ b = f % '(a, b)
  fmap f = repMap @f (obj @a :**: f)
data family Curry :: ((i, j) +-> k) -> (i +-> F.FUN j k)
instance (Representable f, CategoryOf i, CategoryOf j) => FunctorForRep (Curry f :: i +-> F.FUN j k) where
  type Curry f @ a = F.SUB (Rep (CurryH f a))
  fmap f = F.Sub (F.Prof \(Rep @_ @_ @c g) -> Rep (repMap @f (f :**: obj @c) . g)) \\ f
data family Apply :: (F.FUN j k, j) +-> k
instance (CategoryOf j, CategoryOf k) => FunctorForRep (Apply :: (F.FUN j k, j) +-> k) where
  type Apply @ '(f, x) = UN F.SUB f % x
  fmap (n :**: f) = n F.! f
instance Closed (BI FUNK) where
  type B j ~~> B k = B (F.FUN j k)
  withObExp r = r
  curry (Bi @(FUN f)) = Bi @(FUN (Rep (Curry f)))
  apply = Bi @(FUN (Rep Apply))

instance (Bicategory kk) => EnrichedProfunctor (BI FUNK) (Bi :: CAT (BI kk)) where
  type ProObj (BI FUNK) (Bi :: CAT (BI kk)) (B j) (B k) = B (kk j k)
  withProObj r = r
  underlying (Bi @f) = Bi @(FUN (Rep (Constant f)))
  enriched (Bi @(FUN p)) = withObRep @p @'() (Bi @(p % '()))
  rmap = Bi @(FUN (Rep Comp))
  lmap = Bi @(FUN (Rep Comp :.: Rep Swap))
