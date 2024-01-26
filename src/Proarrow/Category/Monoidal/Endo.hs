{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Monoidal.Endo where


import Proarrow.Core (Promonad(..), CategoryOf(..), Profunctor(..), UN, Is, CAT, dimapDefault)
import Proarrow.Category.Bicategory (Bicategory(..))
import Proarrow.Category.Bicategory qualified as B
import Proarrow.Category.Monoidal (Monoidal(..))


type data ENDO (kk :: CAT j) (k :: j) = E (kk k k)
type instance UN E (E p) = p

type Endo :: forall {kk} {k}. CAT (ENDO kk k)
data Endo p q where
  Endo :: p ~> q -> Endo (E p) (E q)

mkEndo :: CategoryOf (kk k k) => (p :: kk k k) ~> q -> Endo (E p) (E q)
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

-- | The monoidal subcategory of a bicategory for a single object.
instance (Bicategory kk, Ob0 kk k) => Monoidal (ENDO kk k) where
  type Unit = E I
  type E p ** E q = E (p `O` q)
  Endo f `par` Endo g = mkEndo (f `o` g)
  leftUnitor (Endo p) = mkEndo (B.leftUnitor p)
  leftUnitorInv (Endo p) = mkEndo (B.leftUnitorInv p)
  rightUnitor (Endo p) = mkEndo (B.rightUnitor p)
  rightUnitorInv (Endo p) = mkEndo (B.rightUnitorInv p)
  associator (Endo p) (Endo q) (Endo r) = mkEndo (B.associator p q r)
  associatorInv (Endo p) (Endo q) (Endo r) = mkEndo (B.associatorInv p q r)