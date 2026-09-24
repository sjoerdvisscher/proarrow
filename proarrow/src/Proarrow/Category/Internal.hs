{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal categories: @ik \`InternalIn\` k@ is a category internal to @k@, given by an object of
-- objects @'C0' ik@, an object of arrows @'C1' ik@, and source\/target\/identity\/composition
-- structure maps.
--
-- Internal to finite sets these are the finite categories, and each direction needs a different
-- presentation of finite sets. A 'FiniteCat' counts its arrows only at the value level, so it is
-- internal to 'Proarrow.Category.Instance.FinHask.FINHASK'. Going back,
-- 'Proarrow.Category.Enriched.Thin.Enumerable' wants the object list as a type, which only the
-- skeleton 'Proarrow.Category.Instance.FinSet.FINSET' supplies, so 'INTERNAL' is built from an
-- internal category in @FINSET@.
module Proarrow.Category.Internal where

import Prelude (($))
import Prelude qualified as P

import Data.Fin (fin0, fin1, fin2, toNatural)
import Data.Kind (Type)
import Data.List (elemIndex, genericIndex, genericLength)
import Data.Proxy (Proxy (..))
import Data.Type.Nat (Nat2, Nat3, SNatI, reify, snat)
import Data.Type.Nat qualified as N
import Data.Universe.Class qualified as U
import Data.Vec.Lazy (Vec (..))
import Data.Vec.Lazy qualified as Vec
import Numeric.Natural (Natural)
import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, indices)
import Proarrow.Category.Enriched.Thin
  ( At
  , AtOb (..)
  , Enumerable (..)
  , Finite (..)
  , FmapWrap
  , Index
  , Indexed (..)
  , IndexedList (..)
  , MapWrap
  , Objects
  , finite
  , withWrapAtLookup
  , wrapFinite
  )
import Proarrow.Category.Instance.Bool (BOOL)
import Proarrow.Category.Instance.FinHask (FINHASK (..), arr)
import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Category.Instance.Ordinal (IsOrdinal, ORDINAL)
import Proarrow.Core (CAT, CategoryOf (..), Hom, Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, (\\))
import Proarrow.Profunctor.Instance.Cone (Cone (..), Cosink (..))

-- | An internal category in a category @k@.
class ik `InternalIn` k where
  type C0 ik :: k
  type C1 ik :: k
  source :: C1 ik ~> (C0 ik :: k)
  target :: C1 ik ~> (C0 ik :: k)
  identity :: C0 ik ~> (C1 ik :: k)
  compose :: Cosink [C1 ik, C1 ik, C1 ik :: k] -- first arrow projection, second arrow projection, composite

-- | >>> import Data.Fin
-- >>> import Data.Type.Nat
-- >>> import Data.Vec.Lazy
-- >>> import Proarrow.Limit.Pullback
-- >>> import Prelude qualified as P
-- >>> (pullback (source @BOOL @FINSET) (target @BOOL @FINSET) \(FinSet l) (FinSet r) -> P.show (l, r)) :: P.String
-- "(0 ::: 1 ::: 2 ::: 2 ::: VNil,0 ::: 0 ::: 1 ::: 2 ::: VNil)"
instance BOOL `InternalIn` FINSET where
  type C0 BOOL = FS Nat2 -- Fin0 = FLS, Fin1 = TRU
  type C1 BOOL = FS Nat3 -- Fin0 = Fls, Fin1 = F2T, Fin2 = Tru
  source = FinSet $ fin0 ::: fin0 ::: fin1 ::: VNil
  target = FinSet $ fin0 ::: fin1 ::: fin1 ::: VNil
  identity = FinSet $ fin0 ::: fin2 ::: VNil

  -- 4 different ways to compose, read vertically.
  compose =
    Cone $
      Leg (FinSet $ fin0 ::: fin1 ::: fin2 ::: fin2 ::: VNil) $
        Leg (FinSet $ fin0 ::: fin0 ::: fin1 ::: fin2 ::: VNil) $
          Leg
            (FinSet $ fin0 ::: fin1 ::: fin1 ::: fin2 ::: VNil)
            Apex

-- * Finite categories are the ones internal to @FINHASK@

-- | An object of @k@ as an inhabitant of a finite Haskell type: its index in
-- @'Proarrow.Category.Enriched.Thin.Objects' k@.
type ObIx :: Kind -> Type
newtype ObIx k = ObIx Natural
  deriving newtype (P.Eq, P.Ord, P.Show)

-- | An arrow of @k@ as an inhabitant of a finite Haskell type: the indices of its source and target
-- objects, and its own position in that hom-set.
type ArrIx :: Kind -> Type
data ArrIx k = ArrIx {arrSrc :: Natural, arrTgt :: Natural, arrPos :: Natural}
  deriving (P.Eq, P.Ord, P.Show)

-- | A composable pair, and the apex of 'compose': the pullback of 'source' along 'target'. The
-- arrows are given outer first, so that the legs of 'compose' come out in the order that instance
-- wants them: the first leg composed after the second.
type CompIx :: Kind -> Type
data CompIx k = CompIx (ArrIx k) (ArrIx k)
  deriving (P.Eq, P.Ord, P.Show)

-- | How many objects @k@ has, by walking its object list.
obCount :: forall k. (Enumerable k) => Natural
obCount = go (finite @k)
  where
    go :: IndexedList (xs :: [k]) -> Natural
    go FNil = 0
    go (FCons xs) = 1 P.+ go xs

-- | Recover the object sitting at an index, together with the 'Ob' evidence that lets the
-- 'Finitary' methods be called at it. The index must be below 'obCount'; every index the
-- enumerations below produce is.
withObIx :: forall k r. (Enumerable k) => Natural -> (forall (a :: k). (Ob a) => Proxy a -> r) -> r
withObIx i f = reify (N.fromNatural i) \(_ :: Proxy n) -> case atOb @k (snat @n) of
  AtJust @_ @a -> f (Proxy @a)
  AtNothing -> P.error "withObIx: no object at this index"

-- | The size of a hom-set, named by the indices of its endpoints.
homSize :: forall k. (FiniteCat k) => Natural -> Natural -> Natural
homSize i j =
  withObIx @k i \(_ :: Proxy a) ->
    withObIx @k j \(_ :: Proxy b) ->
      size @(Hom k) @a @b

instance (Enumerable k) => U.Universe (ObIx k) where
  universe = ObIx P.<$> indices (obCount @k)
instance (Enumerable k) => U.Finite (ObIx k)

instance (FiniteCat k) => U.Universe (ArrIx k) where
  universe =
    [ ArrIx i j h
    | i <- indices (obCount @k)
    , j <- indices (obCount @k)
    , h <- indices (homSize @k i j)
    ]
instance (FiniteCat k) => U.Finite (ArrIx k)

instance (FiniteCat k) => U.Universe (CompIx k) where
  universe = [CompIx g f | g <- U.universeF, f <- U.universeF, arrSrc g P.== arrTgt f]
instance (FiniteCat k) => U.Finite (CompIx k)

-- | Every finite category is a category internal to 'FINHASK': objects and arrows are carried by
-- their indices, and the structure maps are the lookup tables that read those indices back.
--
-- At 'BOOL' every table agrees with the hand-written @FINSET@ presentation above, with the arrows
-- coming out in the order @Fls@, @F2T@, @Tru@.
--
-- >>> import Data.List (elemIndex)
-- >>> import Proarrow.Category.Instance.FinHask (toList)
-- >>> let ix a = P.maybe (-1) P.id (elemIndex a (U.universeF :: [ArrIx BOOL])) :: P.Int
-- >>> P.map P.snd (toList (source @BOOL @FINHASK))
-- [0,0,1]
-- >>> P.map P.snd (toList (target @BOOL @FINHASK))
-- [0,1,1]
-- >>> P.map (ix P.. P.snd) (toList (identity @BOOL @FINHASK))
-- [0,2]
-- >>> :{
-- (case compose @BOOL @FINHASK of
--    Cone (Leg l1 (Leg l2 (Leg l3 Apex))) ->
--      let g l = P.map (ix P.. P.snd) (toList l) in (g l1, g l2, g l3))
--   :: ([P.Int], [P.Int], [P.Int])
-- :}
-- ([0,1,2,2],[0,0,1,2],[0,1,1,2])
instance (FiniteCat k) => k `InternalIn` FINHASK where
  type C0 k = FH (ObIx k)
  type C1 k = FH (ArrIx k)
  source = arr \(ArrIx i _ _) -> ObIx i
  target = arr \(ArrIx _ j _) -> ObIx j
  identity = arr \(ObIx i) -> withObIx @k i \(_ :: Proxy a) -> ArrIx i i (toIndex @(Hom k) @a @a id)
  compose =
    Cone $
      Leg (arr \(CompIx f _) -> f) $
        Leg (arr \(CompIx _ g) -> g) $
          Leg (arr composite) Apex
    where
      composite (CompIx (ArrIx j l g) (ArrIx i _ f)) =
        withObIx @k i \(_ :: Proxy a) ->
          withObIx @k j \(_ :: Proxy b) ->
            withObIx @k l \(_ :: Proxy c) ->
              ArrIx i l (toIndex @(Hom k) @a @c (fromIndex @(Hom k) @b @c g . fromIndex @(Hom k) @a @b f))

-- * The converse: an internal category in @FINSET@ is a finite category

-- | How many objects and how many arrows an internal category in @FINSET@ has. These are types.
-- That is what @FINSET@ has over 'Proarrow.Category.Instance.FinHask.FINHASK', and the converse
-- needs it, because 'Enumerable' asks for its object list at the type level.
type NumObs ik = UN FS (C0 ik :: FINSET)

type NumArrs ik = UN FS (C1 ik :: FINSET)

-- | The category an internal category in @FINSET@ presents, as a kind: its objects are the elements
-- of @'C0' ik@, numbered by 'ORDINAL'.
type data INTERNAL ik = IN (ORDINAL (NumObs ik))

-- | An arrow of the presented category: an element of @'C1' ik@. That its 'source' and 'target' are
-- the objects claimed is a runtime invariant, as the table invariants of 'FinSet' are.
type Internal :: forall {ik}. CAT (INTERNAL ik)
data Internal a b where
  Internal :: (Ob a, Ob b) => Natural -> Internal (a :: INTERNAL ik) b

-- | A structure map as a list of indices into its codomain.
tableOf :: FinSet a b -> [Natural]
tableOf (FinSet v) = P.map toNatural (Vec.toList v)

-- | The composition table: for each composable pair, the outer arrow, the inner arrow, and their
-- composite, as indices into @'C1' ik@.
compTable :: forall ik. (ik `InternalIn` FINSET) => [(Natural, Natural, Natural)]
compTable = case compose @ik @FINSET of
  Cone (Leg l1 (Leg l2 (Leg l3 Apex))) -> P.zip3 (tableOf l1) (tableOf l2) (tableOf l3)

-- | Which element of @'C0' ik@ an object names.
obNum :: forall {ik} (a :: INTERNAL ik). (Enumerable (INTERNAL ik), Ob a) => Natural
obNum = withIndex @(INTERNAL ik) @a (N.reflectToNum (Proxy @(Index a)))

instance (ik `InternalIn` FINSET) => Indexed (INTERNAL ik) where
  type Index (a :: INTERNAL ik) = Index (UN IN a)
  type At (INTERNAL ik) i = FmapWrap IN (At (ORDINAL (NumObs ik)) i)

instance (ik `InternalIn` FINSET, SNatI (NumObs ik)) => Finite (INTERNAL ik) where
  type Objects (INTERNAL ik) = MapWrap IN (Objects (ORDINAL (NumObs ik)))
  finite = wrapFinite @IN
  withAtLookup = withWrapAtLookup @IN

instance (ik `InternalIn` FINSET, SNatI (NumObs ik)) => Enumerable (INTERNAL ik) where
  withIndex @a r = withIndex @(ORDINAL (NumObs ik)) @(UN IN a) r
  atOb i = case atOb @(ORDINAL (NumObs ik)) i of
    AtJust -> AtJust
    AtNothing -> AtNothing

instance (ik `InternalIn` FINSET, SNatI (NumObs ik)) => Profunctor (Internal :: CAT (INTERNAL ik)) where
  dimap = dimapDefault
  r \\ Internal{} = r

instance (ik `InternalIn` FINSET, SNatI (NumObs ik)) => Promonad (Internal :: CAT (INTERNAL ik)) where
  id @a = Internal (genericIndex (tableOf (identity @ik @FINSET)) (obNum @a))
  Internal g . Internal f = case [c | (o, i, c) <- compTable @ik, o P.== g, i P.== f] of
    c : _ -> Internal c
    [] -> P.error "Internal.(.): the arrows do not compose"

instance (ik `InternalIn` FINSET, SNatI (NumObs ik)) => CategoryOf (INTERNAL ik) where
  type (~>) = Internal
  type Ob a = (Is IN a, IsOrdinal (UN IN a))

instance (ik `InternalIn` FINSET, SNatI (NumObs ik)) => Finitary (Internal :: CAT (INTERNAL ik)) where
  elements @a @b =
    [ Internal e
    | (e, s, t) <- P.zip3 [0 ..] (tableOf (source @ik @FINSET)) (tableOf (target @ik @FINSET))
    , s P.== obNum @a
    , t P.== obNum @b
    ]
  size @a @b = genericLength (elements @(Internal :: CAT (INTERNAL ik)) @a @b)
  toIndex @a @b (Internal e) =
    case elemIndex e [n | Internal n <- elements @(Internal :: CAT (INTERNAL ik)) @a @b] of
      P.Just i -> P.fromIntegral i
      P.Nothing -> P.error "Internal.toIndex: not an arrow of this hom-set"
  fromIndex @a @b i = genericIndex (elements @(Internal :: CAT (INTERNAL ik)) @a @b) i

-- | The converse, as a statement: an internal category in @FINSET@ presents a 'FiniteCat'.
--
-- At 'BOOL' the presented category has the hom-sets of 'BOOL' back: one arrow each way except from
-- @TRU@ to @FLS@, where there is none.
--
-- >>> import Proarrow.Category.Instance.Ordinal (ORDINAL (..))
-- >>> :{
-- [ size @(Hom (INTERNAL BOOL)) @(IN OZ) @(IN OZ)
-- , size @(Hom (INTERNAL BOOL)) @(IN OZ) @(IN (OS OZ))
-- , size @(Hom (INTERNAL BOOL)) @(IN (OS OZ)) @(IN OZ)
-- , size @(Hom (INTERNAL BOOL)) @(IN (OS OZ)) @(IN (OS OZ))
-- ] :: [Natural]
-- :}
-- [1,1,0,1]
--
-- >>> let f = fromIndex @(Hom (INTERNAL BOOL)) @(IN OZ) @(IN (OS OZ)) 0
-- >>> toIndex @(Hom (INTERNAL BOOL)) @(IN OZ) @(IN (OS OZ)) (id @_ @(IN (OS OZ)) . f)
-- 0
internalIsFinite
  :: forall ik r. (ik `InternalIn` FINSET, SNatI (NumObs ik)) => ((FiniteCat (INTERNAL ik)) => r) -> r
internalIsFinite r = r
