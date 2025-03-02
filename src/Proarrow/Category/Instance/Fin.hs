module Proarrow.Category.Instance.Fin where

import Proarrow.Core (CAT, CategoryOf (..), Obj, Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))

type data NAT = Z | S NAT

type data FIN n where
  FZ :: FIN (S n)
  FS :: FIN (S n) -> FIN (S (S n))

type FIN0 = FIN Z
type FIN1 = FIN (S Z)
type FIN2 = FIN (S (S Z))
type FIN3 = FIN (S (S (S Z)))

type LTE :: forall {n :: NAT}. CAT (FIN n)
data LTE a b where
  ZEQ :: LTE FZ FZ
  ZLT :: LTE FZ b -> LTE FZ (FS b)
  SLT :: LTE a b -> LTE (FS a) (FS b)

absurdL :: (a :: FIN Z) ~> b
absurdL @a = case obj @a of {}

absurdR :: a ~> (b :: FIN Z)
absurdR @_ @b = case obj @b of {}

class IsFin (a :: FIN n) where
  finId :: Obj a
instance IsFin (a :: FIN Z) where
  finId = finId
instance IsFin FZ where
  finId = ZEQ
instance (IsFin b) => IsFin (FS b) where
  finId = SLT finId

instance Profunctor LTE where
  dimap = dimapDefault
  r \\ ZEQ = r
  r \\ ZLT b = r \\ b
  r \\ SLT ab = r \\ ab
instance Promonad LTE where
  id = finId
  ZEQ . ZEQ = ZEQ
  ZLT b . ZEQ = ZLT b
  SLT ab . ZLT za = ZLT (ab . za)
  SLT ab . SLT bc = SLT (ab . bc)
instance CategoryOf (FIN n) where
  type (~>) = LTE
  type Ob a = IsFin a

class IsLTE (a :: FIN n) (b :: FIN n) where
  lte :: a ~> b
instance IsLTE FZ FZ where
  lte = ZEQ
instance (IsLTE FZ b) => IsLTE FZ (FS b) where
  lte = ZLT lte
instance (IsLTE a b) => IsLTE (FS a) (FS b) where
  lte = SLT lte
instance ThinProfunctor LTE where
  type HasArrow LTE a b = IsLTE a b
  arr = lte
  withArr ZEQ r = r
  withArr (ZLT b) r = withArr b r
  withArr (SLT ab) r = withArr ab r

instance HasInitialObject (FIN (S n)) where
  type InitialObject = FZ
  initiate' ZEQ = ZEQ
  initiate' (ZLT b) = ZLT b
  initiate' (SLT ab) = ZLT (initiate' ab)

instance HasTerminalObject (FIN (S Z)) where
  type TerminalObject = FZ
  terminate' ZEQ = ZEQ

instance (HasTerminalObject (FIN (S n))) => HasTerminalObject (FIN (S (S n))) where
  type TerminalObject = FS TerminalObject
  terminate' ZEQ = ZLT (terminate' ZEQ)
  terminate' (ZLT b) = ZLT (terminate' b)
  terminate' (SLT ab) = SLT (terminate' ab)

instance HasBinaryCoproducts (FIN Z) where
  type a || b = a
  withObCoprod r = r
  lft = absurdR
  rgt = absurdR
  (|||) = \case {}

instance HasBinaryCoproducts (FIN (S Z)) where
  type FZ || FZ = FZ
  withObCoprod @a @b r = case (obj @a, obj @b) of (ZEQ, ZEQ) -> r
  lft @a @b = case (obj @a, obj @b) of (ZEQ, ZEQ) -> ZEQ
  rgt @a @b = case (obj @a, obj @b) of (ZEQ, ZEQ) -> ZEQ
  ZEQ ||| ZEQ = ZEQ

-- | Maximum
instance (HasBinaryCoproducts (FIN (S n))) => HasBinaryCoproducts (FIN (S (S n))) where
  type FZ || b = b
  type a || FZ = a
  type FS a || FS b = FS (a || b)
  withObCoprod @a @b r = case obj @a of
    ZEQ -> r
    SLT @a' a -> case obj @b of
      ZEQ -> r
      SLT @b' b -> withObCoprod @(FIN (S n)) @a' @b' r \\ a \\ b

  lft @a @b = case (obj @a, obj @b) of
    (ZEQ, ZEQ) -> ZEQ
    (ZEQ, SLT b) -> ZLT (initiate' b)
    (a, ZEQ) -> a
    (SLT @a' ab, SLT @b' b) -> SLT (lft @_ @a' @b' \\ ab \\ b)

  rgt @a @b = case (obj @a, obj @b) of
    (ZEQ, ZEQ) -> ZEQ
    (SLT a, ZEQ) -> ZLT (initiate' a)
    (ZEQ, b) -> b
    (SLT @a' a, SLT @b' ab) -> SLT (rgt @_ @a' @b' \\ a \\ ab)

  ZEQ ||| ZEQ = ZEQ
  ZLT ZEQ ||| a = a
  a ||| ZLT ZEQ = a
  ZLT a@ZLT{} ||| ZLT b@ZLT{} = ZLT (a ||| b)
  ZLT a@ZLT{} ||| SLT bc = SLT (a ||| bc)
  SLT ab ||| ZLT c@ZLT{} = SLT (ab ||| c)
  SLT a ||| SLT b = SLT (a ||| b)

instance HasBinaryProducts (FIN Z) where
  type a && b = a
  withObProd r = r
  fst = absurdR
  snd = absurdR
  (&&&) = \case {}

instance HasBinaryProducts (FIN (S Z)) where
  type FZ && FZ = FZ
  withObProd @a @b r = case (obj @a, obj @b) of (ZEQ, ZEQ) -> r
  fst @a @b = case (obj @a, obj @b) of (ZEQ, ZEQ) -> ZEQ
  snd @a @b = case (obj @a, obj @b) of (ZEQ, ZEQ) -> ZEQ
  ZEQ &&& ZEQ = ZEQ

-- | Minimum
instance (HasBinaryProducts (FIN (S n))) => HasBinaryProducts (FIN (S (S n))) where
  type FZ && b = FZ
  type a && FZ = FZ
  type FS a && FS b = FS (a && b)
  withObProd @a @b r = case obj @a of
    ZEQ -> r
    SLT @a' a -> case obj @b of
      ZEQ -> r
      SLT @b' b -> withObProd @(FIN (S n)) @a' @b' r \\ a \\ b

  fst @a @b = case (obj @a, obj @b) of
    (ZEQ, ZEQ) -> ZEQ
    (ZEQ, SLT _) -> ZEQ
    (a , ZEQ) -> initiate' a
    (SLT @a' l, SLT @b' r) -> SLT (fst @_ @a' @b' \\ l \\ r)

  snd @a @b = case (obj @a, obj @b) of
    (ZEQ, ZEQ) -> ZEQ
    (SLT _, ZEQ) -> ZEQ
    (ZEQ, b) -> initiate' b
    (SLT @a' l, SLT @b' r) -> SLT (snd @_ @a' @b' \\ l \\ r)

  ZEQ &&& ZEQ = ZEQ
  ZLT _ &&& ZEQ = ZEQ
  ZEQ &&& ZLT _ = ZEQ
  ZLT a &&& ZLT b = ZLT (a &&& b)
  SLT a &&& SLT b = SLT (a &&& b)