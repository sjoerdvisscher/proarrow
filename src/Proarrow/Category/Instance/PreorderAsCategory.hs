module Proarrow.Category.Instance.PreorderAsCategory where

import Data.Kind (Constraint)

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor, Promonad (..), UN, dimapDefault)
import Proarrow.Core qualified as Core
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.BinaryProduct qualified as P
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Preorder (CProfunctor (..), CPromonad (..), PreorderOf (..), (\\))
import Proarrow.Preorder.Constraint ()
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))

newtype POCATK k = PC k
type instance UN PC (PC k) = k

data PoAsCat a b where
  PoAsCat :: (a <= b) => PoAsCat (PC a) (PC b)

instance (PreorderOf k) => Profunctor (PoAsCat :: CAT (POCATK k)) where
  dimap = dimapDefault
  r \\ PoAsCat @a @b = r \\ obs @((<=) @k) @a @b
instance (PreorderOf k) => Promonad (PoAsCat :: CAT (POCATK k)) where
  id @a = PoAsCat \\ cid @((<=) @k) @(UN PC a)
  (.) @b @c @a PoAsCat PoAsCat = PoAsCat \\ ccomp @((<=) @k) @(UN PC a) @(UN PC b) @(UN PC c)
instance (PreorderOf k) => CategoryOf (POCATK k) where
  type (~>) = PoAsCat
  type Ob a = (Is PC a, COb (UN PC a))

instance (PreorderOf k) => ThinProfunctor (PoAsCat :: CAT (POCATK k)) where
  type HasArrow PoAsCat (PC a) (PC b) = a <= b
  arr = PoAsCat
  withArr PoAsCat r = r

instance HasTerminalObject (POCATK Constraint) where
  type TerminalObject = PC (() :: Constraint)
  terminate' PoAsCat = PoAsCat

instance HasBinaryProducts (POCATK Constraint) where
  type l && r = PC ((UN PC l, UN PC r) :: Constraint)
  fst' PoAsCat PoAsCat = PoAsCat
  snd' PoAsCat PoAsCat = PoAsCat
  PoAsCat &&& PoAsCat = PoAsCat

instance MonoidalProfunctor (PoAsCat :: CAT (POCATK Constraint)) where
  par0 = id
  f `par` g = f *** g

instance Monoidal (POCATK Constraint) where
  type Unit = TerminalObject
  type a ** b = a && b
  leftUnitor = P.leftUnitorProd
  leftUnitorInv = P.leftUnitorProdInv
  rightUnitor = P.rightUnitorProd
  rightUnitorInv = P.rightUnitorProdInv
  associator = P.associatorProd
  associatorInv = P.associatorProdInv
