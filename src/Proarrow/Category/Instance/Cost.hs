{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Instance.Cost where

import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, withSomeSNat, natVal, withKnownNat, type SNat, type (+), cmpNat)
import Data.Type.Ord (type Max, type Min, OrderingI (..), type (<=))
import Unsafe.Coerce (unsafeCoerce)
import Prelude (Num ((+)), error, ($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, (//), obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Object.Initial (HasInitialObject (..))

type data COST = C Nat | INF

data SCost n where
  SC :: (KnownNat n) => SCost (C n)
  SINF :: SCost INF

type GTE :: CAT COST
data GTE a b where
  Inf :: (Ob a) => GTE INF a
  GTE :: (KnownNat a, KnownNat b, b <= a) => GTE (C a) (C b)

lteTrans :: forall (a :: Nat) b c r. (a <= b, b <= c, KnownNat a, KnownNat c) => ((a <= c) => r) -> r
lteTrans r = case cmpNat (Proxy :: Proxy a) (Proxy :: Proxy c) of
  LTI -> r
  EQI -> r
  GTI -> error "lteTrans: broken transitivity"

plusMonotone
  :: forall (a :: Nat) b c d r. (a <= b, c <= d, KnownNat (a + c), KnownNat (b + d)) => (((a + c) <= (b + d)) => r) -> r
plusMonotone r = case cmpNat (Proxy :: Proxy (a + c)) (Proxy :: Proxy (b + d)) of
  LTI -> r
  EQI -> r
  GTI -> error "plusMonotone: broken monotonicity"

withPlusIsNat :: forall a b r. (KnownNat a, KnownNat b) => ((KnownNat (a + b)) => r) -> r
withPlusIsNat = withKnownNat ab
  where
    ab :: SNat (a + b)
    ab = withSomeSNat (natVal (Proxy :: Proxy a) + natVal (Proxy :: Proxy b)) unsafeCoerce

class IsCost (a :: COST) where
  sing :: SCost a
instance (KnownNat n) => IsCost (C n) where
  sing = SC
instance IsCost INF where
  sing = SINF

instance Profunctor GTE where
  dimap = dimapDefault
  r \\ Inf = r
  r \\ GTE = r
instance Promonad GTE where
  id @a = case sing @a of
    SINF -> Inf
    SC -> GTE
  f . Inf = Inf \\ f
  GTE @b @c . GTE @a = lteTrans @c @b @a GTE
-- | Cost category. Categories enriched in the cost category are lawvere metric spaces.
instance CategoryOf COST where
  type (~>) = GTE
  type Ob a = (IsCost a)

instance HasTerminalObject COST where
  type TerminalObject = C 0
  terminate @a = case sing @a of
    SINF -> Inf
    SC @b -> case cmpNat (Proxy :: Proxy 0) (Proxy :: Proxy b) of
      LTI -> GTE
      EQI -> GTE
      GTI -> error "terminate: found a Nat smaller than 0"

instance HasInitialObject COST where
  type InitialObject = INF
  initiate = Inf

instance HasBinaryProducts COST where
  type INF && b = INF
  type a && INF = INF
  type C a && C b = C (Max a b)
  withObProd @a @b r = case (sing @a, sing @b) of
    (SINF, _) -> r
    (_, SINF) -> r
    (SC @a', SC @b') -> case cmpNat (Proxy :: Proxy a') (Proxy :: Proxy b') of
      LTI -> r
      EQI -> r
      GTI -> r
  fst @a @b = case (sing @a, sing @b) of
    (SINF, _) -> Inf
    (_, SINF) -> Inf
    (SC @a', SC @b') -> case cmpNat (Proxy :: Proxy a') (Proxy :: Proxy b') of
      LTI -> GTE
      EQI -> GTE
      GTI -> GTE
  snd @a @b = case (sing @a, sing @b) of
    (SINF, _) -> Inf
    (_, SINF) -> Inf
    (SC @a', SC @b') -> case (cmpNat (Proxy :: Proxy a') (Proxy :: Proxy b'), cmpNat (Proxy :: Proxy b') (Proxy :: Proxy a')) of
      (LTI, _) -> GTE
      (EQI, _) -> GTE
      (GTI, LTI) -> GTE
      (GTI, GTI) -> error "snd: found 2 nats greater than eachother"
  (&&&) @_ @x @y l r = l // r // withObProd @_ @x @y $ case (l, r) of
    (Inf, _) -> Inf
    (GTE @_ @x', GTE @_ @y') -> case cmpNat (Proxy :: Proxy x') (Proxy :: Proxy y') of
      LTI -> GTE
      EQI -> GTE
      GTI -> GTE

instance HasBinaryCoproducts COST where
  type INF || b = b
  type a || INF = a
  type C a || C b = C (Min a b)
  withObCoprod @a @b r = case (sing @a, sing @b) of
    (SINF, _) -> r
    (_, SINF) -> r
    (SC @a', SC @b') -> case cmpNat (Proxy :: Proxy a') (Proxy :: Proxy b') of
      LTI -> r
      EQI -> r
      GTI -> r
  lft @a @b = case (sing @a, sing @b) of
    (SINF, _) -> Inf
    (_, SINF) -> id
    (SC @a', SC @b') -> case (cmpNat (Proxy :: Proxy a') (Proxy :: Proxy b'), cmpNat (Proxy :: Proxy b') (Proxy :: Proxy a')) of
      (LTI, _) -> GTE
      (EQI, _) -> GTE
      (GTI, LTI) -> GTE
      (GTI, GTI) -> error "lft: found 2 nats greater than eachother"
  rgt @a @b = case (sing @a, sing @b) of
    (SINF, _) -> id
    (_, SINF) -> Inf
    (SC @a', SC @b') -> case cmpNat (Proxy :: Proxy a') (Proxy :: Proxy b') of
      LTI -> GTE
      EQI -> GTE
      GTI -> GTE
  (|||) @x @y l r = l // r // withOb2 @_ @x @y $ case (l, r) of
    (Inf, _) -> r
    (_, Inf) -> l
    (GTE @x', GTE @y') -> case cmpNat (Proxy :: Proxy x') (Proxy :: Proxy y') of
      LTI -> GTE
      EQI -> GTE
      GTI -> GTE

instance MonoidalProfunctor GTE where
  par0 = GTE
  par :: forall x1 x2 y1 y2. GTE x1 x2 -> GTE y1 y2 -> GTE (x1 ** y1) (x2 ** y2)
  l `par` r = case (l, r) of
    (Inf, _) -> r // withOb2 @_ @x2 @y2 Inf
    (_, Inf) -> l // withOb2 @_ @x2 @y2 Inf
    (GTE @a @b, GTE @c @d) -> withPlusIsNat @a @c $ withPlusIsNat @b @d $ plusMonotone @b @a @d @c GTE

instance Monoidal COST where
  type Unit = C 0
  type INF ** b = INF
  type a ** INF = INF
  type C a ** C b = C (a + b)
  withOb2 @a @b r = case (sing @a, sing @b) of
    (SC @a', SC @b') -> withPlusIsNat @a' @b' r
    (SINF, _) -> r
    (_, SINF) -> r
  leftUnitor @a = case sing @a of
    SINF -> id
    SC -> GTE
  leftUnitorInv @a = case sing @a of
    SINF -> id
    SC -> GTE
  rightUnitor @a = case sing @a of
    SINF -> id
    SC -> GTE
  rightUnitorInv @a = case sing @a of
    SINF -> id
    SC -> GTE
  associator @a @b @c = case (sing @a, sing @b, sing @c) of
    (SC @a', SC @b', SC @c') -> unsafeCoerce $ withPlusIsNat @a' @b' $ withPlusIsNat @(a' + b') @c' $ obj @(C (a' + b' + c'))
    (SINF, _, _) -> Inf
    (_, SINF, _) -> Inf
    (_, _, SINF) -> Inf
  associatorInv @a @b @c = case (sing @a, sing @b, sing @c) of
    (SC @a', SC @b', SC @c') -> unsafeCoerce $ withPlusIsNat @a' @b' $ withPlusIsNat @(a' + b') @c' $ obj @(C (a' + b' + c'))
    (SINF, _, _) -> Inf
    (_, SINF, _) -> Inf
    (_, _, SINF) -> Inf

instance SymMonoidal COST where
  swap @a @b = case (sing @a, sing @b) of
    (SINF, _) -> Inf
    (_, SINF) -> Inf
    (SC @a', SC @b') -> unsafeCoerce (withPlusIsNat @a' @b' (obj @(C (a' + b'))))

instance Distributive COST where
  distL @a @b @c = case (sing @a, sing @b, sing @c) of
    (SINF, _, _) -> Inf
    (_, SINF, _) -> withOb2 @_ @a @c id
    (_, _, SINF) -> withOb2 @_ @a @b id
    (SC @a', SC @b', SC @c') -> withPlusIsNat @a' @b' $ withPlusIsNat @a' @c' $
      case (cmpNat (Proxy :: Proxy b') (Proxy :: Proxy c'), cmpNat (Proxy :: Proxy (a' + b')) (Proxy :: Proxy (a' + c'))) of
        (LTI, LTI) -> id
        (LTI, GTI) -> error "distL: b is less than c, but a + b is greater than a + c"
        (EQI, _) -> id
        (GTI, LTI) -> error "distL: b is greater than c, but a + b is less than a + c"
        (GTI, GTI) -> id
  distR @a @b @c = case (sing @a, sing @b, sing @c) of
    (SINF, _, _) -> withOb2 @_ @b @c id
    (_, SINF, _) -> withOb2 @_ @a @c id
    (_, _, SINF) -> Inf
    (SC @a', SC @b', SC @c') -> withPlusIsNat @a' @c' $ withPlusIsNat @b' @c' $
      case (cmpNat (Proxy :: Proxy a') (Proxy :: Proxy b'), cmpNat (Proxy :: Proxy (a' + c')) (Proxy :: Proxy (b' + c'))) of
        (LTI, LTI) -> id
        (LTI, GTI) -> error "distR: a is less than b, but a + c is greater than b + c"
        (EQI, _) -> id
        (GTI, LTI) -> error "distR: a is greater than b, but a + c is less than b + c"
        (GTI, GTI) -> id
  distL0 = Inf
  distR0 = Inf