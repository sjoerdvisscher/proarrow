{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.FinSet where

import Data.Fin (Fin (..), fin0, fin1, fin2, split, weakenLeft, weakenRight)
import Data.Maybe (fromMaybe)
import Data.Type.Nat (Mult, Nat (..), Nat0, Nat1, Nat2, Nat3, Plus, SNat (..), SNatI, snat, snatToNatural)
import Data.Vec.Lazy
  ( Vec (..)
  , chunks
  , concat
  , concatMap
  , reifyList
  , repeat
  , tabulate
  , toList
  , universe
  , zipWith
  , (!)
  , (++)
  )
import Prelude (Either (..), Num (..), fromIntegral, ($))
import Prelude qualified as P

import Data.Data (Proxy (..))
import Data.IntMap qualified as IM
import Proarrow.Category.Instance.Bool (BOOL)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Distributive (Distributive (..), distLProd, distRProd)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , diag
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  )
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Pullback (Cone (..), Cosink (..), HasPullbacks (..), InternalIn (..))
import Proarrow.Object.Pushout (Cocone (..), HasPushouts (..), Sink (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Optic (Iso', iso)

type data FINSET = FS Nat
type instance UN FS (FS n) = n

type FinSet :: CAT FINSET
data FinSet a b where
  FinSet :: (SNatI n, SNatI m) => {unFinSet :: Vec n (Fin m)} -> FinSet (FS n) (FS m)

deriving instance P.Show (FinSet a b)
deriving instance P.Eq (FinSet a b)

instance Profunctor FinSet where
  dimap = dimapDefault
  r \\ FinSet{} = r
instance Promonad FinSet where
  id = FinSet universe
  FinSet l . FinSet r = FinSet (P.fmap (l !) r)
instance CategoryOf FINSET where
  type (~>) = FinSet
  type Ob a = (Is FS a, SNatI (UN FS a))

instance HasInitialObject FINSET where
  type InitialObject = FS Nat0
  initiate = FinSet VNil
instance HasBinaryCoproducts FINSET where
  type FS a || FS b = FS (Plus a b)
  withObCoprod @(FS a) @b r = case snat @a of
    SZ -> r
    SS @a' -> withObCoprod @_ @(FS a') @b r
  lft @(FS a) @(FS b) = withObCoprod @_ @(FS a) @(FS b) $ FinSet (P.fmap (weakenLeft (Proxy @b)) universe)
  rgt @(FS a) @(FS b) = withObCoprod @_ @(FS a) @(FS b) $ FinSet (P.fmap (weakenRight (Proxy @a)) universe)
  FinSet @a l ||| FinSet @b r = withObCoprod @_ @(FS a) @(FS b) $ FinSet (l ++ r)

instance HasTerminalObject FINSET where
  type TerminalObject = FS Nat1
  terminate = FinSet (repeat fin0)
instance HasBinaryProducts FINSET where
  type a && b = FS (Mult (UN FS a) (UN FS b))
  withObProd @(FS a) @b r = case snat @a of
    SZ -> r
    SS @a' -> withObProd @_ @(FS a') @b $ withObCoprod @_ @b @(FS (Mult a' (UN FS b))) r
  fst @(FS a) @(FS b) = withObProd @_ @(FS a) @(FS b) $ FinSet (concat @a @b $ P.fmap repeat universe)
  snd @(FS a) @(FS b) = withObProd @_ @(FS a) @(FS b) $ FinSet (concat @a @b $ repeat universe)
  FinSet @_ @a l &&& FinSet @_ @b r = withObProd @_ @(FS a) @(FS b) $ FinSet (zipWith mult l r)

instance Distributive FINSET where
  distL @a @b @c = distLProd @a @b @c
  distR @a @b @c = distRProd @a @b @c
  distL0 @(FS a) = withObProd @_ @(FS a) @(FS Z) $ FinSet (concat @a @Z (repeat VNil))
  distR0 = FinSet VNil

-- >>> import Data.Type.Nat
-- >>> import Data.Fin
-- >>> mult @Nat5 @Nat4 fin4 fin2 -- 4*4+2
-- 18
-- >>> mult @Nat4 @Nat5 fin2 fin4 -- 5*2+4
-- 14
mult :: forall n m. (SNatI n, SNatI m) => Fin n -> Fin m -> Fin (Mult n m)
mult n m = case snat @n of
  SZ -> case n of {}
  SS @n' -> case n of
    FZ -> weakenLeft (Proxy @(Mult n' m)) m
    FS n' -> weakenRight (Proxy @m) (mult n' m)

unmult :: forall n m. (SNatI n, SNatI m) => Fin (Mult n m) -> (Fin n, Fin m)
unmult f = case snat @n of
  SZ -> case f of {}
  SS @n' -> case split @m @(Mult n' m) f of
    P.Left m -> (FZ, m)
    P.Right f' -> let (n, m) = unmult @n' @m f' in (FS n, m)

instance MonoidalProfunctor FinSet where
  par0 = id
  par = (***)

instance Monoidal FINSET where
  type a ** b = a && b
  type Unit = FS Nat1
  withOb2 @a @b = withObProd @_ @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @a @b @c = associatorProd @a @b @c
  associatorInv @a @b @c = associatorProdInv @a @b @c

instance SymMonoidal FINSET where
  swap @a @b = swapProd @a @b

type family Exp (a :: Nat) (b :: Nat) :: Nat where
  Exp a Z = S Z
  Exp a (S n) = Mult a (Exp a n)

instance Closed FINSET where
  type FS a ~~> FS b = FS (Exp b a)
  withObExp @(FS a) @b r = case snat @a of
    SZ -> r
    SS @a' -> withObExp @_ @(FS a') @b $ withObProd @_ @b @(FS (Exp (UN FS b) a')) r
  curry @(FS a) @(FS b) (FinSet @_ @c f) = withObExp @_ @(FS b) @(FS c) $ FinSet (P.fmap exp (chunks @a @b f))
  apply @(FS a) @(FS b) =
    withObExp @_ @(FS a) @(FS b) $
      withObProd @_ @(FS (Exp b a)) @(FS a) $
        FinSet (concatMap @_ @a @_ @(Exp b a) unExp universe)

-- >>> import Data.Type.Nat
-- >>> import Data.Fin
-- >>> exp @_ @Nat2 (fin1 ::: fin0 ::: fin1 ::: fin1 ::: VNil)
-- 11
exp :: forall n m. (SNatI n, SNatI m) => Vec n (Fin m) -> Fin (Exp m n)
exp VNil = FZ
exp (x ::: xs) = case snat @n of
  SS @n' -> withObExp @_ @(FS n') @(FS m) $ mult x (exp @n' @m xs)

-- >>> import Data.Type.Nat
-- >>> import Data.Fin
-- >>> unExp @Nat3 @Nat2 fin6
-- 1 ::: 1 ::: 0 ::: VNil
unExp :: forall n m. (SNatI n, SNatI m) => Fin (Exp m n) -> Vec n (Fin m)
unExp f = case snat @n of
  SZ -> VNil
  SS @n' -> withObExp @_ @(FS n') @(FS m) $ let (x, xs) = unmult @m @(Exp m n') f in x ::: unExp @n' @m xs

-- >>> import Data.Type.Nat
-- >>> comult @(FS Nat4)
-- FinSet (0 ::: 5 ::: 10 ::: 15 ::: VNil)
instance (SNatI a) => Comonoid (FS a) where
  counit = terminate
  comult = diag
instance CopyDiscard FINSET

instance Monoid (FS Nat1) where
  mempty = terminate
  mappend = terminate

findIso :: (SNatI n) => [(Fin n, Fin n)] -> P.Maybe (Iso' (FS n) (FS n))
findIso ps = iso P.<$> findArr ps P.<*> findArr (P.fmap swap ps)

findArr :: forall n. (SNatI n) => [(Fin n, Fin n)] -> P.Maybe (FS n ~> FS n)
findArr = go (repeat P.Nothing)
  where
    go :: Vec n (P.Maybe (Fin n)) -> [(Fin n, Fin n)] -> P.Maybe (FS n ~> FS n)
    go v [] = P.Just $ FinSet $ zipWith fromMaybe universe v
    go v ((f1, f2) : ps) = case v ! f1 of
      P.Just f | f P./= f2 -> P.Nothing
      _ -> go (tabulate (\i -> if i P.== f1 then P.Just f2 else v ! i)) ps

-- Exercise 3.84 of Seven Sketches (A: 0=red, 1=blue, 2=black)
-- >>> import Data.Fin
-- >>> import Data.Type.Nat
-- >>> import Data.Vec.Lazy
-- >>> let f :: FinSet (FS Nat6) (FS Nat3) = FinSet $ fin0 ::: fin1 ::: fin0 ::: fin0 ::: fin2 ::: fin1 ::: VNil
-- >>> let g :: FinSet (FS Nat4) (FS Nat3) = FinSet $ fin2 ::: fin0 ::: fin1 ::: fin0 ::: VNil
-- >>> (case pullback f g of Cone (Leg (FinSet l) (Leg (FinSet r) Apex)) -> P.show (l, r)) :: P.String
-- "(0 ::: 0 ::: 1 ::: 2 ::: 2 ::: 3 ::: 3 ::: 4 ::: 5 ::: VNil,1 ::: 3 ::: 2 ::: 1 ::: 3 ::: 1 ::: 3 ::: 0 ::: 2 ::: VNil)"
instance HasPullbacks FINSET where
  pullback (FinSet f) (FinSet g) =
    let groups = [(x, y) | x <- toList universe, y <- toList universe, f ! x P.== g ! y]
    in reifyList groups \vec -> Cone $ Leg (FinSet $ P.fmap fst vec) $ Leg (FinSet $ P.fmap snd vec) Apex

-- >>> import Data.Fin
-- >>> import Data.Type.Nat
-- >>> import Data.Vec.Lazy
-- >>> import Proarrow.Object.Pullback (equalizer)
-- >>> let f :: FinSet (FS Nat4) (FS Nat3) = FinSet $ fin0 ::: fin1 ::: fin1 ::: fin0 ::: VNil
-- >>> let g :: FinSet (FS Nat4) (FS Nat3) = FinSet $ fin2 ::: fin0 ::: fin1 ::: fin0 ::: VNil
-- >>> (case equalizer f g of Cone (Leg (FinSet f) Apex) -> P.show f) :: P.String
-- "2 ::: 3 ::: VNil"

-- Exercise 6.22 of Seven Sketches
-- >>> import Data.Fin
-- >>> import Data.Type.Nat
-- >>> let l :: FinSet (FS Nat4) (FS Nat3) = FinSet $ fin0 ::: fin0 ::: fin1 ::: fin2 ::: VNil
-- >>> let r :: FinSet (FS Nat4) (FS Nat5) = FinSet $ fin0 ::: fin2 ::: fin4 ::: fin4 ::: VNil
-- >>> (case pushout l r of Cospan (FinSet l) (FinSet r) -> (P.show l, P.show r)) :: (P.String, P.String)
-- ("1 ::: 3 ::: 3 ::: VNil","1 ::: 0 ::: 1 ::: 2 ::: 3 ::: VNil")
instance HasPushouts FINSET where
  pushout (FinSet @_ @a f) (FinSet @_ @b g) =
    let
      sizeA = fromIntegral (snatToNatural (snat @a))
      sizeB = fromIntegral (snatToNatural (snat @b))
      toI (Left a) = fromIntegral a
      toI (Right b) = sizeA + fromIntegral b
      find m i = P.maybe i (find m) $ IM.lookup i m
      union m (i, j) = let ri = find m i; rj = find m j in if ri P.== rj then m else IM.insert ri rj m
      unionFind = P.foldl union IM.empty (zipWith (\u v -> (toI (Left u), toI (Right v))) f g)
      groups = IM.elems $ P.foldl @[] (\m x -> IM.insertWith (P.++) (find unionFind x) [x] m) IM.empty [0 .. sizeA + sizeB - 1]
    in
      reifyList groups \vec ->
        let mapA = tabulate @a (\a -> findIndex (P.elem (toI $ Left a)) vec)
            mapB = tabulate @b (\b -> findIndex (P.elem (toI $ Right b)) vec)
        in Cocone $ Coleg (FinSet mapA) $ Coleg (FinSet mapB) Coapex

findIndex :: (a -> P.Bool) -> Vec n a -> Fin n
findIndex _ VNil = P.error "unexpected missing element"
findIndex f (a ::: as)
  | f a = FZ
  | P.otherwise = FS $ findIndex f as

-- >>> import Data.Fin
-- >>> import Data.Type.Nat
-- >>> import Data.Vec.Lazy
-- >>> (case pullback (source @BOOL @FINSET) (target @BOOL @FINSET) of Cone (Leg (FinSet l) (Leg (FinSet r) Apex)) -> P.show (l, r)) :: P.String
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
          Leg (FinSet $ fin0 ::: fin1 ::: fin1 ::: fin2 ::: VNil) $
            Apex

type Finite k = k `InternalIn` FINSET
