module Proarrow.Category.Instance.Bool where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  )
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Preorder.ThinCategory (Thin (..))

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

class IsBoolArr (a :: BOOL) b where boolArr :: a ~> b
instance IsBoolArr FLS FLS where boolArr = Fls
instance IsBoolArr FLS TRU where boolArr = F2T
instance IsBoolArr TRU TRU where boolArr = Tru

instance Thin BOOL where
  type HasArrow a b = IsBoolArr a b
  arr = boolArr
  withArr Fls r = r
  withArr F2T r = r
  withArr Tru r = r

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
  fst' F2T Fls = F2T
  fst' F2T Tru = F2T
  snd' Fls Fls = Fls
  snd' Fls Tru = F2T
  snd' Tru Fls = Fls
  snd' Tru Tru = Tru
  snd' Fls F2T = F2T
  snd' Tru F2T = F2T
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
  lft' F2T Fls = F2T
  lft' F2T Tru = F2T
  rgt' Fls Fls = Fls
  rgt' Fls Tru = Tru
  rgt' Tru Fls = F2T
  rgt' Tru Tru = Tru
  rgt' Fls F2T = F2T
  rgt' Tru F2T = F2T
  Fls ||| Fls = Fls
  F2T ||| F2T = F2T
  F2T ||| Tru = Tru
  Tru ||| F2T = Tru
  Tru ||| Tru = Tru

instance MonoidalProfunctor Booleans where
  par0 = id
  f `par` g = f *** g

instance Monoidal BOOL where
  type Unit = TerminalObject
  type a ** b = a && b
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

instance Monoid TRU where
  mempty = Tru
  mappend = Tru

instance Comonoid TRU where
  counit = Tru
  comult = Tru

instance Comonoid FLS where
  counit = F2T
  comult = Fls