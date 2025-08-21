module Proarrow.Category.Instance.Bool where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Monoid (Comonoid (..), CopyDiscard, Monoid (..))
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
import Proarrow.Object.Dual (ExpSA, StarAutonomous (..), applySA, currySA)
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Category.Enriched.ThinCategory (ThinProfunctor (..))

data BOOL = FLS | TRU

type Booleans :: CAT BOOL
data Booleans a b where
  Fls :: Booleans FLS FLS
  F2T :: Booleans FLS TRU
  Tru :: Booleans TRU TRU

class (IsBool (Dual b)) => IsBool (b :: BOOL) where boolId :: b ~> b
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
  withObProd @a r = case obj @a of
    Tru -> r
    Fls -> r
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
  withObCoprod @a r = case obj @a of
    Tru -> r
    Fls -> r
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

-- | Products as monoidal structure.
instance Monoidal BOOL where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 @a @b = withObProd @BOOL @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @a @b @c = associatorProd @a @b @c
  associatorInv @a @b @c = associatorProdInv @a @b @c

instance SymMonoidal BOOL where
  swap @a @b = swapProd @a @b

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
  type a ~~> b = ExpSA a b
  withObExp @a r = case obj @a of
    Fls -> r
    Tru -> r
  curry @a @b = currySA @a @b
  apply @b @c = applySA @b @c

instance StarAutonomous BOOL where
  type Dual FLS = TRU
  type Dual TRU = FLS
  dual Fls = Tru
  dual F2T = F2T
  dual Tru = Fls
  dualInv @a @b f = case (obj @a, obj @b, f) of
    (Fls, Fls, Tru) -> Fls
    (Tru, Fls, F2T) -> F2T
    (Tru, Tru, Fls) -> Tru
    (Fls, Tru, f') -> case f' of {}
  linDist @a @b f = case (obj @a, obj @b) of
    (Fls, Fls) -> F2T
    (Tru, Fls) -> Tru
    (_, Tru) -> f
  linDistInv @_ @b @c f = case (obj @b, obj @c) of
    (Fls, Fls) -> F2T
    (Fls, Tru) -> Fls
    (Tru, _) -> f

-- BOOL is not CompactClosed

instance Monoid TRU where
  mempty = Tru
  mappend = Tru

instance (Ob a) => Comonoid (a :: BOOL) where
  counit = case obj @a of
    Fls -> F2T
    Tru -> Tru
  comult = case obj @a of
    Fls -> Fls
    Tru -> Tru

instance CopyDiscard BOOL
