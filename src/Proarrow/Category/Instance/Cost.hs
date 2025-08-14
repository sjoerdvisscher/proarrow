{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Cost where

import Data.Proxy (Proxy (..))
import GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , cmpNat
  , natVal
  , withSomeSNat
  , pattern SNat
  , type SNat
  , type (+)
  , type (<=)
  )
import Unsafe.Coerce (unsafeCoerce)
import Prelude (Num ((+)), error, ($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, (//), obj)

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
withPlusIsNat r = case ab of SNat -> r
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