module Proarrow.Category.Instance.FinSet where

import Data.Fin (Fin (..), fin0, split, weakenLeft, weakenRight)
import Data.Type.Nat (Mult, Nat (..), Nat0, Nat1, Plus, SNat (..), SNatI, snat)
import Data.Vec.Lazy (Vec (..), chunks, concat, concatMap, repeat, universe, zipWith, (!), (++))
import Prelude (($))
import Prelude qualified as P

import Data.Data (Proxy (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Distributive (Distributive (..), distLProd, distRProd)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
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
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))

type data FINSET = FS Nat
type instance UN FS (FS n) = n

type FinSet :: CAT FINSET
data FinSet a b where
  FinSet :: (SNatI n, SNatI m) => { unFinSet :: Vec n (Fin m) } -> FinSet (FS n) (FS m)

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
instance SNatI a => Comonoid (FS a) where
  counit = terminate
  comult = diag
instance CopyDiscard FINSET

instance Monoid (FS Nat1) where
  mempty = terminate
  mappend = terminate