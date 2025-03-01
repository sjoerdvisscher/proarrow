{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Endo where

import Proarrow.Category.Bicategory (Bicategory (..), Comonad (..), Monad (..))
import Proarrow.Category.Bicategory qualified as B
import Proarrow.Category.Bicategory.Kan (LeftKanExtension (..), RightKanExtension (..), dimapRan)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.Coexponential (Coclosed (..))
import Proarrow.Object.Exponential (Closed (..))

type data ENDO (kk :: CAT j) (k :: j) = E (kk k k)
type instance UN E (E p) = p

type Endo :: forall {kk} {k}. CAT (ENDO kk k)
data Endo p q where
  Endo :: p ~> q -> Endo (E p) (E q)

mkEndo :: (CategoryOf (kk k k)) => (p :: kk k k) ~> q -> Endo (E p) (E q)
mkEndo pq = Endo pq \\ pq

instance (Bicategory kk, Ob0 kk k) => Profunctor (Endo :: CAT (ENDO kk k)) where
  dimap = dimapDefault
  r \\ Endo f = r \\ f
instance (Bicategory kk, Ob0 kk k) => Promonad (Endo :: CAT (ENDO kk k)) where
  id = Endo id
  Endo m . Endo n = Endo (m . n)
instance (Bicategory kk, Ob0 kk k) => CategoryOf (ENDO kk k) where
  type (~>) = Endo
  type Ob p = (Is E p, Ob (UN E p))

instance (Bicategory kk, Ob0 kk k, (Ob (I :: kk k k))) => MonoidalProfunctor (Endo :: CAT (ENDO kk k)) where
  par0 = Endo iObj
  Endo f `par` Endo g = mkEndo (f `o` g)

-- | The monoidal subcategory of a bicategory for a single object.
instance (Bicategory kk, Ob0 kk k, (Ob (I :: kk k k))) => Monoidal (ENDO kk k) where
  type Unit = E I
  type E p ** E q = E (p `O` q)
  withOb2 @(E a) @(E b) r = r \\\ (obj @a `o` obj @b)
  leftUnitor = mkEndo B.leftUnitor
  leftUnitorInv = mkEndo B.leftUnitorInv
  rightUnitor = mkEndo B.rightUnitor
  rightUnitorInv = mkEndo B.rightUnitorInv
  associator @(E p) @(E q) @(E r) = mkEndo (B.associator @kk @p @q @r)
  associatorInv @(E p) @(E q) @(E r) = mkEndo (B.associatorInv @kk @p @q @r)

instance
  (Bicategory kk, Ob0 kk k, Ob (I :: kk k k), forall (f :: kk k k) (g :: kk k k). (Ob f, Ob g) => RightKanExtension f g)
  => Closed (ENDO kk k)
  where
  type E f ~~> E g = E (Ran f g)
  curry' (Endo @g g) (Endo @j j) (Endo h) = Endo (ranUniv @j @_ @g h) \\ g \\ j \\ h
  uncurry' (Endo @j j) (Endo @f f) (Endo h) = Endo (ran @j @f . (h `o` j)) \\ j \\ f
  (^^^) (Endo f) (Endo g) = Endo (dimapRan g f) \\ f \\ g

instance
  (Bicategory kk, Ob0 kk k, Ob (I :: kk k k), forall (f :: kk k k) (g :: kk k k). (Ob f, Ob g) => LeftKanExtension f g)
  => Coclosed (ENDO kk k)
  where
  type E f <~~ E g = E (Lan g f)
  coeval' (Endo @g g) (Endo @j j) = Endo (lan @j @g) \\ g \\ j
  coevalUniv' (Endo @j j) (Endo @f f) (Endo h) = Endo (lanUniv @j @_ @f h) \\ j \\ f \\ h

-- | Monads are monoids in the category of endo-1-cells.
instance (Bicategory kk, Ob (I :: kk a a), Monad m, Ob m) => Monoid (E m :: ENDO kk a) where
  mempty = mkEndo eta
  mappend = mkEndo mu

-- | Comonads are comonoids in the category of endo-1-cells.
instance (Bicategory kk, Ob (I :: kk a a), Comonad c, Ob c) => Comonoid (E c :: ENDO kk a) where
  counit = mkEndo epsilon
  comult = mkEndo delta
