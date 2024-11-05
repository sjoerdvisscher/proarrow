module Proarrow.Category.Instance.Bool where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct (Distributive (..), HasBinaryCoproducts (..))
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
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))

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

instance ThinProfunctor Booleans where
  type HasArrow Booleans a b = IsBoolArr a b
  arr = boolArr
  withArr Fls r = r
  withArr F2T r = r
  withArr Tru r = r

instance HasTerminalObject BOOL where
  type TerminalObject = TRU
  terminate' Fls = F2T
  terminate' F2T = F2T
  terminate' Tru = Tru

instance HasBinaryProducts BOOL where
  type TRU && b = b
  type FLS && b = FLS
  type a && TRU = a
  type a && FLS = FLS
  fst' Fls _ = Fls
  fst' F2T _ = F2T
  fst' Tru b = terminate' b
  snd' _ Fls = Fls
  snd' _ F2T = F2T
  snd' a Tru = terminate' a
  Fls &&& _ = Fls
  F2T &&& b = b
  Tru &&& Tru = Tru

instance HasInitialObject BOOL where
  type InitialObject = FLS
  initiate' Fls = Fls
  initiate' F2T = F2T
  initiate' Tru = F2T

instance HasBinaryCoproducts BOOL where
  type FLS || b = b
  type TRU || b = TRU
  type a || FLS = a
  type a || TRU = TRU
  lft' Fls b = initiate' b
  lft' F2T _ = F2T
  lft' Tru _ = Tru
  rgt' a Fls = initiate' a
  rgt' _ Tru = Tru
  rgt' _ F2T = F2T
  Fls ||| Fls = Fls
  F2T ||| b = b
  Tru ||| _ = Tru

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

instance Distributive BOOL where
  distL' Fls _ _ = Fls
  distL' F2T b c = initiate' (b +++ c)
  distL' Tru b c = b +++ c
  distR' _ _ Fls = Fls
  distR' a b F2T = initiate' (a +++ b)
  distR' a b Tru = a +++ b
  distL0' _ = Fls
  distR0' _ = Fls

instance Closed BOOL where
  type FLS ~~> b = TRU
  type a ~~> TRU = TRU
  type TRU ~~> FLS = FLS
  curry' Fls Fls _ = F2T
  curry' Fls Tru Fls = Fls
  curry' Fls Tru F2T = F2T
  curry' Tru Fls _ = Tru
  curry' Tru Tru Tru = Tru
  uncurry' Fls c _ = initiate' c
  uncurry' Tru Fls a = a
  uncurry' Tru Tru a = a
  _ ^^^ Fls = Tru
  Tru ^^^ _ = Tru
  Fls ^^^ Tru = Fls
  Fls ^^^ F2T = F2T
  F2T ^^^ F2T = F2T
  F2T ^^^ Tru = F2T

instance Monoid TRU where
  mempty = Tru
  mappend = Tru

instance Comonoid TRU where
  counit = Tru
  comult = Tru

instance Comonoid FLS where
  counit = F2T
  comult = Fls