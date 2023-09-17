module Proarrow.Category.Instance.Bool where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..))
import Proarrow.Object.Exponential (CartesianClosed(..))

-- Redefined here so we don't get orphan instances
data Bool = False | True

type Booleans :: CAT Bool
data Booleans a b where
  Fls :: Booleans False False
  F2T :: Booleans False True
  Tru :: Booleans True True

type instance (~>) = Booleans

class IsBool (b :: Bool) where boolId :: b ~> b
instance IsBool False where boolId = Fls
instance IsBool True where boolId = Tru

instance Category Booleans where
  type Ob b = IsBool b
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


instance HasTerminalObject Bool where
  type TerminalObject = True
  terminate' Fls = F2T
  terminate' Tru = Tru

instance HasBinaryProducts Bool where
  type True && True = True
  type False && True = False
  type True && False = False
  type False && False = False
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

instance HasInitialObject Bool where
  type InitialObject = False
  initiate' Fls = Fls
  initiate' Tru = F2T

instance HasBinaryCoproducts Bool where
  type False || False = False
  type False || True = True
  type True || False = True
  type True || True = True
  left' Fls Fls = Fls
  left' Fls Tru = F2T
  left' Tru Fls = Tru
  left' Tru Tru = Tru
  right' Fls Fls = Fls
  right' Fls Tru = Tru
  right' Tru Fls = F2T
  right' Tru Tru = Tru
  Fls ||| Fls = Fls
  F2T ||| F2T = F2T
  F2T ||| Tru = Tru
  Tru ||| F2T = Tru
  Tru ||| Tru = Tru

instance CartesianClosed Bool where
  type False ~~> False = True
  type False ~~> True = True
  type True ~~> False = False
  type True ~~> True = True
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