-- | The finite ordinal @n@ as a thin category: the kind @'ORDINAL' n@ has objects @'OZ', 'OS' 'OZ',
-- ...@ (@n@ of them), with an arrow @a '~>' b@ exactly when @a <= b@ ('LTE') -- the linear order
-- on @n@ elements. Small enough that (co)equalizers can be computed by explicit case analysis.
module Proarrow.Category.Instance.Ordinal where

import Data.Kind (Constraint, Type)
import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat)
import Prelude (Maybe (..), type (~))

import Proarrow.Category.Enriched.Thin
  ( AtOb (..)
  , DecidableProfunctor (..)
  , Decision (..)
  , Enumerable (..)
  , Finite (..)
  , FmapWrap
  , Indexed (..)
  , IndexedList (..)
  , Lookup
  , MapWrap
  , ThinProfunctor (..)
  , mapDecision
  , mapWrap
  , withLookupMapWrap
  )
import Proarrow.Category.Instance.Bool (BOOL (..))
import Proarrow.Category.Topos (HasEpiMonoFactorization (..))
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

type data ORDINAL n where
  OZ :: ORDINAL (S n)
  OS :: ORDINAL (S n) -> ORDINAL (S (S n))

type ORDINAL0 = ORDINAL Z
type ORDINAL1 = ORDINAL (S Z)
type ORDINAL2 = ORDINAL (S (S Z))
type ORDINAL3 = ORDINAL (S (S (S Z)))

type LTE :: forall {n :: Nat}. CAT (ORDINAL n)
data LTE a b where
  ZEQ :: LTE OZ OZ
  ZLT :: LTE OZ b -> LTE OZ (OS b)
  SLT :: LTE a b -> LTE (OS a) (OS b)

-- | @'ORDINAL' 'Z'@ is the empty ordinal, so an object of it is a contradiction: @'LTE' a a@ has
-- no constructor that can match at this kind, and the empty case discharges any goal.
absurdL :: forall (a :: ORDINAL Z) b. (Ob a) => a ~> b
absurdL = case obj @a of {}

absurdR :: forall a (b :: ORDINAL Z). (Ob b) => a ~> b
absurdR = case obj @b of {}

type SOrdinal :: forall {n :: Nat}. ORDINAL n -> Type
data SOrdinal a where
  SOZ :: SOrdinal OZ
  SOS :: (IsOrdinal a) => SOrdinal (OS a)

type IsOrdinal :: forall {n :: Nat}. ORDINAL n -> Constraint
class IsOrdinal (a :: ORDINAL n) where
  singOrdinal :: SOrdinal a
instance IsOrdinal OZ where
  singOrdinal = SOZ
instance (IsOrdinal b) => IsOrdinal (OS b) where
  singOrdinal = SOS

-- | Each ordinal is numbered by itself: @'OZ'@ is zero and @'OS'@ the successor.
type OrdIndex :: forall {n :: Nat}. ORDINAL n -> Nat
type family OrdIndex a where
  OrdIndex OZ = Z
  OrdIndex (OS a) = S (OrdIndex a)

type OrdAt :: forall (n :: Nat) -> Nat -> Maybe (ORDINAL n)
type family OrdAt n i where
  OrdAt Z i = 'Nothing
  OrdAt (S n) Z = 'Just OZ
  OrdAt (S Z) (S i) = 'Nothing
  OrdAt (S (S n)) (S i) = FmapWrap OS (OrdAt (S n) i)

-- | The ordinals of @'ORDINAL' n@, in order.
type OrdObjects :: forall (n :: Nat) -> [ORDINAL n]
type family OrdObjects n where
  OrdObjects Z = '[]
  OrdObjects (S Z) = '[OZ]
  OrdObjects (S (S n)) = OZ ': MapWrap OS (OrdObjects (S n))

instance Indexed (ORDINAL n) where
  type Index (a :: ORDINAL n) = OrdIndex a
  type At (ORDINAL n) i = OrdAt n i

instance (SNatI n) => Finite (ORDINAL n) where
  type Objects (ORDINAL n) = OrdObjects n
  finite = withOrdObjects @n SZ P.id
  withAtLookup i r = withOrdObjects @n i (P.const r)

-- | An ordinal count is none, one, or more. It needs three cases, and not the two of 'Nat', because
-- @'OS'@ lands in @'ORDINAL' ('S' ('S' n))@, so @'ORDINAL' ('S' 'Z')@ holds only @'OZ'@.
ordSize
  :: forall n r
   . (SNatI n)
  => ((n ~ Z) => r) -> ((n ~ S Z) => r) -> (forall m. (n ~ S (S m), SNatI m) => r) -> r
ordSize none one more = case snat @n of
  SZ -> none
  SS @m -> case snat @m of
    SZ -> one
    SS -> more

-- | The ordinals of @'ORDINAL' n@ together with the proof that the list tabulates 'OrdAt' at one index.
-- The two are produced by the same recursion, so each level builds the shorter list once and both
-- the proof and the longer list use it.
withOrdObjects
  :: forall n i r
   . (SNatI n)
  => SNat i -> ((Lookup (OrdObjects n) i ~ OrdAt n i) => IndexedList (OrdObjects n) -> r) -> r
withOrdObjects i k =
  ordSize @n
    (k FNil)
    (case i of SZ -> k (FCons FNil); SS -> k (FCons FNil))
    ( \ @m -> case i of
        SZ -> withOrdObjects @(S m) SZ \xs -> k (FCons (mapWrap @OS xs))
        SS @i' -> withOrdObjects @(S m) (snat @i') \xs ->
          withLookupMapWrap @OS (snat @i') xs (k (FCons (mapWrap @OS xs)))
    )

-- | The ordinal at an index, if there is one. 'Enumerable' cannot go through the generic 'atOb',
-- which is defined in terms of the very 'withOb' being given here, so the walk is done by recursion
-- on the index instead of on the object list.
ordAtOb :: forall n i. (SNatI n) => SNat i -> AtOb (ORDINAL n) (OrdAt n i)
ordAtOb i =
  ordSize @n
    AtNothing
    (case i of SZ -> AtJust; SS -> AtNothing)
    ( \ @m -> case i of
        SZ -> AtJust
        SS @i' -> case ordAtOb @(S m) (snat @i') of
          AtNothing -> AtNothing
          AtJust -> AtJust
    )

instance (SNatI n) => Enumerable (ORDINAL n) where
  withIndex @a r = case singOrdinal @a of
    SOZ -> r
    SOS @a' -> case snat @n of SS -> withIndex @_ @a' r
  atOb = ordAtOb

instance Profunctor LTE where
  dimap = dimapDefault
  r \\ ZEQ = r
  r \\ ZLT b = r \\ b
  r \\ SLT ab = r \\ ab
instance Promonad LTE where
  id @a = case singOrdinal @a of
    SOZ -> ZEQ
    SOS -> SLT id
  ZEQ . ZEQ = ZEQ
  ZLT b . ZEQ = ZLT b
  SLT ab . ZLT za = ZLT (ab . za)
  SLT ab . SLT bc = SLT (ab . bc)

-- | The (thin) category of finite ordinals. An arrow from a to b means that a is less than or equal to b.
instance CategoryOf (ORDINAL n) where
  type (~>) = LTE
  type Ob a = IsOrdinal a

-- | @a <= b@ on the ordinal, as a 'BOOL'.
type OrdLeq :: forall {n :: Nat}. ORDINAL n -> ORDINAL n -> BOOL
type family OrdLeq a b where
  OrdLeq OZ b = TRU
  OrdLeq (OS a) OZ = FLS
  OrdLeq (OS a) (OS b) = OrdLeq a b

instance ThinProfunctor LTE

instance DecidableProfunctor LTE where
  type Holds LTE a b = OrdLeq a b
  decide @a @b = case (singOrdinal @a, singOrdinal @b) of
    (SOZ, SOZ) -> Yes ZEQ
    (SOZ, SOS @b') -> mapDecision ZLT (decide @LTE @OZ @b')
    (SOS, SOZ) -> No
    (SOS @a', SOS @b') -> mapDecision SLT (decide @LTE @a' @b')
  toHolds ZEQ r = r
  toHolds (ZLT b) r = toHolds b r
  toHolds (SLT ab) r = toHolds ab r

instance HasInitialObject (ORDINAL (S n)) where
  type InitialObject = OZ
  initiate @a = case singOrdinal @a of
    SOZ -> ZEQ
    SOS @a' -> ZLT (initiate @_ @a')

instance HasTerminalObject (ORDINAL (S Z)) where
  type TerminalObject = OZ
  terminate @a = case singOrdinal @a of SOZ -> ZEQ

instance (HasTerminalObject (ORDINAL (S n))) => HasTerminalObject (ORDINAL (S (S n))) where
  type TerminalObject = OS TerminalObject
  terminate @a = case singOrdinal @a of
    SOZ -> ZLT terminate
    SOS @a' -> SLT (terminate @_ @a')

instance HasBinaryCoproducts (ORDINAL Z) where
  type a || b = a
  withObCoprod r = r
  lft = absurdR
  rgt = absurdR
  (|||) = \case {}

instance HasBinaryCoproducts (ORDINAL (S Z)) where
  type OZ || OZ = OZ
  withObCoprod @a @b r = case (singOrdinal @a, singOrdinal @b) of (SOZ, SOZ) -> r
  lft @a @b = case (singOrdinal @a, singOrdinal @b) of (SOZ, SOZ) -> ZEQ
  rgt @a @b = case (singOrdinal @a, singOrdinal @b) of (SOZ, SOZ) -> ZEQ
  ZEQ ||| ZEQ = ZEQ

-- | Maximum
instance (HasBinaryCoproducts (ORDINAL (S n))) => HasBinaryCoproducts (ORDINAL (S (S n))) where
  type OZ || b = b
  type a || OZ = a
  type OS a || OS b = OS (a || b)
  withObCoprod @a @b r = case singOrdinal @a of
    SOZ -> r
    SOS @a' -> case singOrdinal @b of
      SOZ -> r
      SOS @b' -> withObCoprod @(ORDINAL (S n)) @a' @b' r

  lft @a @b = case singOrdinal @b of
    SOZ -> obj @a
    SOS @b' -> case singOrdinal @a of
      SOZ -> ZLT (initiate @_ @b')
      SOS @a' -> SLT (lft @_ @a' @b')

  rgt @a @b = case singOrdinal @a of
    SOZ -> obj @b
    SOS @a' -> case singOrdinal @b of
      SOZ -> ZLT (initiate @_ @a')
      SOS @b' -> SLT (rgt @_ @a' @b')

  ZEQ ||| ZEQ = ZEQ
  ZLT ZEQ ||| a = a
  a ||| ZLT ZEQ = a
  ZLT a@ZLT{} ||| ZLT b@ZLT{} = ZLT (a ||| b)
  ZLT a@ZLT{} ||| SLT bc = SLT (a ||| bc)
  SLT ab ||| ZLT c@ZLT{} = SLT (ab ||| c)
  SLT a ||| SLT b = SLT (a ||| b)

instance HasBinaryProducts (ORDINAL Z) where
  type a && b = a
  withObProd r = r
  fst = absurdR
  snd = absurdR
  (&&&) = \case {}

instance HasBinaryProducts (ORDINAL (S Z)) where
  type OZ && OZ = OZ
  withObProd @a @b r = case (singOrdinal @a, singOrdinal @b) of (SOZ, SOZ) -> r
  fst @a @b = case (singOrdinal @a, singOrdinal @b) of (SOZ, SOZ) -> ZEQ
  snd @a @b = case (singOrdinal @a, singOrdinal @b) of (SOZ, SOZ) -> ZEQ
  ZEQ &&& ZEQ = ZEQ

-- | Minimum
instance (HasBinaryProducts (ORDINAL (S n))) => HasBinaryProducts (ORDINAL (S (S n))) where
  type OZ && b = OZ
  type a && OZ = OZ
  type OS a && OS b = OS (a && b)
  withObProd @a @b r = case singOrdinal @a of
    SOZ -> r
    SOS @a' -> case singOrdinal @b of
      SOZ -> r
      SOS @b' -> withObProd @_ @a' @b' r

  fst @a @b = case singOrdinal @b of
    SOZ -> initiate @_ @a
    SOS @b' -> case singOrdinal @a of
      SOZ -> ZEQ
      SOS @a' -> SLT (fst @_ @a' @b')

  snd @a @b = case singOrdinal @a of
    SOZ -> initiate @_ @b
    SOS @a' -> case singOrdinal @b of
      SOZ -> ZEQ
      SOS @b' -> SLT (snd @_ @a' @b')

  ZEQ &&& ZEQ = ZEQ
  ZLT _ &&& ZEQ = ZEQ
  ZEQ &&& ZLT _ = ZEQ
  ZLT a &&& ZLT b = ZLT (a &&& b)
  SLT a &&& SLT b = SLT (a &&& b)

-- | @LTE@ is thin, so equalizers are trivial; @factorEqualizer incl h@ just needs @h@'s domain to be
-- @<=@ @incl@'s domain, which -- since both share the codomain @x@ -- can only fail when @incl@'s
-- domain is @OZ@ (nothing below it) but @h@'s domain is a successor (necessarily above @OZ@).
instance HasEqualizers (ORDINAL n) where
  equalize = thinEqualize
  factorEqualizer ZEQ ZEQ = ZEQ
  factorEqualizer (ZLT _) (ZLT _) = ZEQ
  factorEqualizer (SLT @e0 incl) (ZLT _) = ZLT (initiate @_ @e0 \\ incl)
  factorEqualizer (SLT incl) (SLT h) = SLT (factorEqualizer incl h)
  factorEqualizer (ZLT _) (SLT _) = P.error "factorEqualizer: h's image must lie within incl's image"

-- | Dual to the 'HasEqualizers' instance above.
instance HasCoequalizers (ORDINAL n) where
  coequalize = thinCoequalize
  factorCoequalizer ZEQ ZEQ = ZEQ
  factorCoequalizer ZEQ (ZLT @c0' h) = ZLT (initiate @_ @c0' \\ h)
  factorCoequalizer (ZLT _) ZEQ = P.error "factorCoequalizer: h must be constant on q's fibers"
  factorCoequalizer (ZLT q) (ZLT h) = SLT (factorCoequalizer q h)
  factorCoequalizer (SLT q) (SLT h) = SLT (factorCoequalizer q h)

-- | Pullbacks in a thin category are just meets; computed directly (rather than via 'Proarrow.Limit.Pullback.thinPullback',
-- which would need @HasProducts (ORDINAL n)@ -- unavailable for an abstract @n@, since 'HasBinaryProducts'
-- and 'HasTerminalObject' are only resolvable for a syntactically concrete @n@).
instance HasPullbacks (ORDINAL n) where
  pullback (ZLT _) (ZLT _) k = k ZEQ ZEQ
  pullback (ZLT _) (SLT @b' g) k = k ZEQ (ZLT (initiate @_ @b' \\ g))
  pullback (SLT @a' f) (ZLT _) k = k (ZLT (initiate @_ @a' \\ f)) ZEQ
  pullback (SLT f) (SLT g) k = pullback f g \p1 p2 -> k (SLT p1) (SLT p2)
  pullback ZEQ ZEQ k = k ZEQ ZEQ

  -- @p1@ and @k1@ already share a codomain (@a@), which is all 'factorEqualizer' needs to compare
  -- @q@ against @p@ -- @p2@/@k2@ carry no extra information once @p1, p2@ are known to be a pullback.
  factorPullback p1 _ k1 _ = factorEqualizer p1 k1

-- | Dual to the 'HasPullbacks' instance above: pushouts in a thin category are joins.
instance HasPushouts (ORDINAL n) where
  pushout ZEQ g k = k g (id \\ g)
  pushout f ZEQ k = k (id \\ f) f
  pushout (ZLT f) (ZLT g) k = pushout f g \q1 q2 -> k (SLT q1) (SLT q2)
  pushout (SLT f) (SLT g) k = pushout f g \q1 q2 -> k (SLT q1) (SLT q2)

  factorPushout p1 _ k1 _ = factorCoequalizer p1 k1

instance HasEpiMonoFactorization (ORDINAL n)
