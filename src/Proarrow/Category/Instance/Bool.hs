module Proarrow.Category.Instance.Bool where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj)
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
  , swapProd'
  )
import Proarrow.Object.Dual (StarAutonomous (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..), initiate)
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate)
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))
import Proarrow.Category.Monoidal.Distributive (Distributive (..))

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
  terminate @a = case obj @a of
    Fls -> F2T
    Tru -> Tru

instance HasBinaryProducts BOOL where
  type TRU && b = b
  type FLS && b = FLS
  type a && TRU = a
  type a && FLS = FLS
  fst @a @b = case obj @a of
    Fls -> Fls
    Tru -> terminate @_ @b
  snd @a @b = case obj @b of
    Fls -> Fls
    Tru -> terminate @_ @a
  Fls &&& _ = Fls
  F2T &&& b = b
  Tru &&& Tru = Tru

instance HasInitialObject BOOL where
  type InitialObject = FLS
  initiate @a = case obj @a of
    Fls -> Fls
    Tru -> F2T

instance HasBinaryCoproducts BOOL where
  type FLS || b = b
  type TRU || b = TRU
  type a || FLS = a
  type a || TRU = TRU
  lft @a @b = case obj @a of
    Fls -> initiate @_ @b
    Tru -> Tru
  rgt @a @b = case obj @b of
    Fls -> initiate @_ @a
    Tru -> Tru
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
  swap' = swapProd'

instance Distributive BOOL where
  distL @a @b @c = case obj @a of
    Fls -> Fls
    Tru -> obj @b +++ obj @c
  distR @a @b @c = case obj @c of
    Fls -> Fls
    Tru -> obj @a +++ obj @b
  distL0 = Fls
  distR0 = Fls

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

instance StarAutonomous BOOL where
  type Bottom = FLS
  bottomObj = Fls
  doubleNeg @a = case obj @a of
    Fls -> Fls
    Tru -> Tru

instance Monoid TRU where
  mempty = Tru
  mappend = Tru

instance Comonoid TRU where
  counit = Tru
  comult = Tru

instance Comonoid FLS where
  counit = F2T
  comult = Fls