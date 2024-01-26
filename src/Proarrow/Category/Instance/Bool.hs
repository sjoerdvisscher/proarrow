module Proarrow.Category.Instance.Bool where

import Proarrow.Core (CAT, CategoryOf(..), Promonad(..), Profunctor(..), dimapDefault)
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..), leftUnitorProd, leftUnitorProdInv, rightUnitorProd, rightUnitorProdInv, associatorProd, associatorProdInv, swapProd)
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..))
import Proarrow.Object.Exponential (Closed(..))
import Proarrow.Category.Monoidal (Monoidal(..), SymMonoidal (..))


data BOOL = FLS | TRU

type Booleans :: CAT BOOL
data Booleans a b where
  Fls :: Booleans FLS FLS
  F2T :: Booleans FLS TRU
  Tru :: Booleans TRU TRU


class IsBool (b :: BOOL) where boolId :: b ~> b
instance IsBool FLS where boolId = Fls
instance IsBool TRU where boolId = Tru

-- | The category of 2 objects and one arrow between them, a.k.a. the walking arrow.
instance CategoryOf BOOL where
  type (~>) = Booleans
  type Ob b = IsBool b

instance Promonad Booleans where
  id = boolId
  Fls . Fls = Fls
  F2T . Fls = F2T
  Tru . F2T = F2T
  Tru . Tru = Tru

instance Profunctor Booleans where
  dimap = dimapDefault
  r \\ Fls = r
  r \\ F2T = r
  r \\ Tru = r


instance HasTerminalObject BOOL where
  type TerminalObject = TRU
  terminate' Fls = F2T
  terminate' Tru = Tru

instance HasBinaryProducts BOOL where
  type TRU && TRU = TRU
  type FLS && TRU = FLS
  type TRU && FLS = FLS
  type FLS && FLS = FLS
  fst' Fls Fls = Fls
  fst' Fls Tru = Fls
  fst' Tru Fls = F2T
  fst' Tru Tru = Tru
  snd' Fls Fls = Fls
  snd' Fls Tru = F2T
  snd' Tru Fls = Fls
  snd' Tru Tru = Tru
  Fls &&& Fls = Fls
  Fls &&& F2T = Fls
  F2T &&& Fls = Fls
  F2T &&& F2T = F2T
  Tru &&& Tru = Tru

instance HasInitialObject BOOL where
  type InitialObject = FLS
  initiate' Fls = Fls
  initiate' Tru = F2T

instance HasBinaryCoproducts BOOL where
  type FLS || FLS = FLS
  type FLS || TRU = TRU
  type TRU || FLS = TRU
  type TRU || TRU = TRU
  lft' Fls Fls = Fls
  lft' Fls Tru = F2T
  lft' Tru Fls = Tru
  lft' Tru Tru = Tru
  rgt' Fls Fls = Fls
  rgt' Fls Tru = Tru
  rgt' Tru Fls = F2T
  rgt' Tru Tru = Tru
  Fls ||| Fls = Fls
  F2T ||| F2T = F2T
  F2T ||| Tru = Tru
  Tru ||| F2T = Tru
  Tru ||| Tru = Tru

instance Monoidal BOOL where
  type Unit = TerminalObject
  type a ** b = a && b
  f `par` g = f *** g
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance SymMonoidal BOOL where
  swap' = swapProd

instance Closed BOOL where
  type FLS ~~> FLS = TRU
  type FLS ~~> TRU = TRU
  type TRU ~~> FLS = FLS
  type TRU ~~> TRU = TRU
  curry' Fls Fls Fls = F2T
  curry' Fls Fls F2T = F2T
  curry' Fls Tru Fls = Fls
  curry' Fls Tru F2T = F2T
  curry' Tru Fls Fls = Tru
  curry' Tru Fls F2T = Tru
  curry' Tru Tru Tru = Tru
  uncurry' Fls Fls F2T = Fls
  uncurry' Fls Fls Tru = Fls
  uncurry' Fls Tru F2T = F2T
  uncurry' Fls Tru Tru = F2T
  uncurry' Tru Fls Fls = Fls
  uncurry' Tru Tru F2T = F2T
  uncurry' Tru Tru Tru = Tru
  Fls ^^^ Fls = Tru
  Fls ^^^ F2T = F2T
  Fls ^^^ Tru = Fls
  F2T ^^^ Fls = Tru
  F2T ^^^ F2T = F2T
  F2T ^^^ Tru = F2T
  Tru ^^^ Fls = Tru
  Tru ^^^ F2T = Tru
  Tru ^^^ Tru = Tru