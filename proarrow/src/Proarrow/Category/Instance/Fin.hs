module Proarrow.Category.Instance.Fin where

import Data.Kind (Constraint, Type)

import Proarrow.Category.Enriched.Thin (ThinProfunctor (..))
import Proarrow.Category.Topos (HasEpiMonoFactorization (..), defaultFactorize)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..), thinCoequalize)
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..), thinEqualize)
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Prelude qualified as P

type data NAT = Z | S NAT

type data FIN n where
  FZ :: FIN (S n)
  FS :: FIN (S n) -> FIN (S (S n))

type FIN0 = FIN Z
type FIN1 = FIN (S Z)
type FIN2 = FIN (S (S Z))
type FIN3 = FIN (S (S (S Z)))

type SFin :: forall {n :: NAT}. FIN n -> Type
data SFin a where
  SZ :: SFin FZ
  SS :: (IsFin a) => SFin (FS a)

type LTE :: forall {n :: NAT}. CAT (FIN n)
data LTE a b where
  ZEQ :: LTE FZ FZ
  ZLT :: LTE FZ b -> LTE FZ (FS b)
  SLT :: LTE a b -> LTE (FS a) (FS b)

absurdL :: (a :: FIN Z) ~> b
absurdL @a = case obj @a of {}

absurdR :: a ~> (b :: FIN Z)
absurdR @_ @b = case obj @b of {}

type IsFin :: forall {n :: NAT}. FIN n -> Constraint
class IsFin (a :: FIN n) where
  singFin :: SFin a
instance IsFin (a :: FIN Z) where
  singFin = singFin
instance IsFin FZ where
  singFin = SZ
instance (IsFin b) => IsFin (FS b) where
  singFin = SS

instance Profunctor LTE where
  dimap = dimapDefault
  r \\ ZEQ = r
  r \\ ZLT b = r \\ b
  r \\ SLT ab = r \\ ab
instance Promonad LTE where
  id @a = case singFin @a of
    SZ -> ZEQ
    SS -> SLT id
  ZEQ . ZEQ = ZEQ
  ZLT b . ZEQ = ZLT b
  SLT ab . ZLT za = ZLT (ab . za)
  SLT ab . SLT bc = SLT (ab . bc)

-- | The (thin) category of finite ordinals. An arrow from a to b means that a is less than or equal to b.
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
  initiate @a = case singFin @a of
    SZ -> ZEQ
    SS @a' -> ZLT (initiate @_ @a')

instance HasTerminalObject (FIN (S Z)) where
  type TerminalObject = FZ
  terminate @a = case singFin @a of SZ -> ZEQ

instance (HasTerminalObject (FIN (S n))) => HasTerminalObject (FIN (S (S n))) where
  type TerminalObject = FS TerminalObject
  terminate @a = case singFin @a of
    SZ -> ZLT terminate
    SS @a' -> SLT (terminate @_ @a')

instance HasBinaryCoproducts (FIN Z) where
  type a || b = a
  withObCoprod r = r
  lft = absurdR
  rgt = absurdR
  (|||) = \case {}

instance HasBinaryCoproducts (FIN (S Z)) where
  type FZ || FZ = FZ
  withObCoprod @a @b r = case (singFin @a, singFin @b) of (SZ, SZ) -> r
  lft @a @b = case (singFin @a, singFin @b) of (SZ, SZ) -> ZEQ
  rgt @a @b = case (singFin @a, singFin @b) of (SZ, SZ) -> ZEQ
  ZEQ ||| ZEQ = ZEQ

-- | Maximum
instance (HasBinaryCoproducts (FIN (S n))) => HasBinaryCoproducts (FIN (S (S n))) where
  type FZ || b = b
  type a || FZ = a
  type FS a || FS b = FS (a || b)
  withObCoprod @a @b r = case singFin @a of
    SZ -> r
    SS @a' -> case singFin @b of
      SZ -> r
      SS @b' -> withObCoprod @(FIN (S n)) @a' @b' r

  lft @a @b = case singFin @b of
    SZ -> obj @a
    SS @b' -> case singFin @a of
      SZ -> ZLT (initiate @_ @b')
      SS @a' -> SLT (lft @_ @a' @b')

  rgt @a @b = case singFin @a of
    SZ -> obj @b
    SS @a' -> case singFin @b of
      SZ -> ZLT (initiate @_ @a')
      SS @b' -> SLT (rgt @_ @a' @b')

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
  withObProd @a @b r = case (singFin @a, singFin @b) of (SZ, SZ) -> r
  fst @a @b = case (singFin @a, singFin @b) of (SZ, SZ) -> ZEQ
  snd @a @b = case (singFin @a, singFin @b) of (SZ, SZ) -> ZEQ
  ZEQ &&& ZEQ = ZEQ

-- | Minimum
instance (HasBinaryProducts (FIN (S n))) => HasBinaryProducts (FIN (S (S n))) where
  type FZ && b = FZ
  type a && FZ = FZ
  type FS a && FS b = FS (a && b)
  withObProd @a @b r = case singFin @a of
    SZ -> r
    SS @a' -> case singFin @b of
      SZ -> r
      SS @b' -> withObProd @_ @a' @b' r

  fst @a @b = case singFin @b of
    SZ -> initiate @_ @a
    SS @b' -> case singFin @a of
      SZ -> ZEQ
      SS @a' -> SLT (fst @_ @a' @b')

  snd @a @b = case singFin @a of
    SZ -> initiate @_ @b
    SS @a' -> case singFin @b of
      SZ -> ZEQ
      SS @b' -> SLT (snd @_ @a' @b')

  ZEQ &&& ZEQ = ZEQ
  ZLT _ &&& ZEQ = ZEQ
  ZEQ &&& ZLT _ = ZEQ
  ZLT a &&& ZLT b = ZLT (a &&& b)
  SLT a &&& SLT b = SLT (a &&& b)

-- | @LTE@ is thin, so equalizers are trivial; @factorEqualizer incl h@ just needs @h@'s domain to be
-- @<=@ @incl@'s domain, which -- since both share the codomain @x@ -- can only fail when @incl@'s
-- domain is @FZ@ (nothing below it) but @h@'s domain is a successor (necessarily above @FZ@).
instance HasEqualizers (FIN n) where
  equalize = thinEqualize
  factorEqualizer ZEQ ZEQ = ZEQ
  factorEqualizer (ZLT _) (ZLT _) = ZEQ
  factorEqualizer (SLT @e0 incl) (ZLT _) = ZLT (initiate @_ @e0 \\ incl)
  factorEqualizer (SLT incl) (SLT h) = SLT (factorEqualizer incl h)
  factorEqualizer (ZLT _) (SLT _) = P.error "factorEqualizer: h's image must lie within incl's image"

-- | Dual to the 'HasEqualizers' instance above.
instance HasCoequalizers (FIN n) where
  coequalize = thinCoequalize
  factorCoequalizer ZEQ ZEQ = ZEQ
  factorCoequalizer ZEQ (ZLT @c0' h) = ZLT (initiate @_ @c0' \\ h)
  factorCoequalizer (ZLT _) ZEQ = P.error "factorCoequalizer: h must be constant on q's fibers"
  factorCoequalizer (ZLT q) (ZLT h) = SLT (factorCoequalizer q h)
  factorCoequalizer (SLT q) (SLT h) = SLT (factorCoequalizer q h)

-- | Pullbacks in a thin category are just meets; computed directly (rather than via 'thinPullback',
-- which would need @HasProducts (FIN n)@ -- unavailable for an abstract @n@, since 'HasBinaryProducts'
-- and 'HasTerminalObject' are only resolvable for a syntactically concrete @n@).
instance HasPullbacks (FIN n) where
  pullback (ZLT _) (ZLT _) k = k ZEQ ZEQ
  pullback (ZLT _) (SLT @b' g) k = k ZEQ (ZLT (initiate @_ @b' \\ g))
  pullback (SLT @a' f) (ZLT _) k = k (ZLT (initiate @_ @a' \\ f)) ZEQ
  pullback (SLT f) (SLT g) k = pullback f g \p1 p2 -> k (SLT p1) (SLT p2)
  pullback ZEQ ZEQ k = k ZEQ ZEQ

  -- @p1@ and @k1@ already share a codomain (@a@), which is all 'factorEqualizer' needs to compare
  -- @q@ against @p@ -- @p2@/@k2@ carry no extra information once @p1, p2@ are known to be a pullback.
  factorPullback p1 _ k1 _ = factorEqualizer p1 k1

-- | Dual to the 'HasPullbacks' instance above: pushouts in a thin category are joins.
instance HasPushouts (FIN n) where
  pushout ZEQ g k = k g (id \\ g)
  pushout f ZEQ k = k (id \\ f) f
  pushout (ZLT f) (ZLT g) k = pushout f g \q1 q2 -> k (SLT q1) (SLT q2)
  pushout (SLT f) (SLT g) k = pushout f g \q1 q2 -> k (SLT q1) (SLT q2)

  factorPushout p1 _ k1 _ = factorCoequalizer p1 k1

instance HasEpiMonoFactorization (FIN n) where
  factorize = defaultFactorize
