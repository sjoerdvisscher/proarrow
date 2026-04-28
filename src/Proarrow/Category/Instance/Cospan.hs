{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Cospan where

import Data.Fin (Fin (..))
import Data.IntMap.Strict qualified as IM
import Data.Type.Nat (snat, snatToNatural)
import Data.Vec.Lazy (Vec (..), reifyList, tabulate, zipWith)
import Prelude (Either (..), Num (..), fromIntegral, ($), (++), (==))
import Prelude qualified as P

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph (ExpHG, Frobenius (..), Hypergraph, applyHG, curryHG, spiderDefault)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, tgt)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct
  ( HasBinaryCoproducts (..)
  , HasCoproducts
  , associatorCoprod
  , associatorCoprodInv
  , leftUnitorCoprod
  , leftUnitorCoprodInv
  , rightUnitorCoprod
  , rightUnitorCoprodInv
  , swapCoprod
  )
import Proarrow.Object.Dual (CompactClosed (..), StarAutonomous (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))

-- | Composition of spans needs a pushout, an inherently dependently typed concept.
-- So we can't express it properly in Haskell, but the injection arrows can still do the right thing.
class (HasCoproducts k) => HasPushouts k where
  pushout :: forall (o :: k) a b. o ~> a -> o ~> b -> Cospan (CS a) (CS b)
  pushout f g = Cospan (lft @k @a @b) (rgt @k @a @b) \\ f \\ g

newtype COSPAN k = CS k
type instance UN CS (CS k) = k

type Cospan :: CAT (COSPAN k)
data Cospan a b where
  Cospan :: forall c a b. a ~> c -> b ~> c -> Cospan (CS a) (CS b)

arr :: (CategoryOf k) => (a :: k) ~> b -> Cospan (CS a) (CS b)
arr f = Cospan f (tgt f)

coarr :: (CategoryOf k) => (a :: k) ~> b -> Cospan (CS b) (CS a)
coarr f = Cospan (tgt f) f

instance (HasPushouts k) => Profunctor (Cospan :: CAT (COSPAN k)) where
  dimap = dimapDefault
  r \\ Cospan f g = r \\ f \\ g
instance (HasPushouts k) => Promonad (Cospan :: CAT (COSPAN k)) where
  id = Cospan id id
  Cospan f g . Cospan h i = case pushout i f of Cospan l r -> Cospan (l . h) (r . g)
instance (HasPushouts k) => CategoryOf (COSPAN k) where
  type (~>) = Cospan
  type Ob a = (Is CS a, Ob (UN CS a))

instance (HasPushouts k) => MonoidalProfunctor (Cospan :: CAT (COSPAN k)) where
  par0 = id
  Cospan l1 l2 `par` Cospan r1 r2 = Cospan (l1 +++ r1) (l2 +++ r2)
instance (HasPushouts k) => Monoidal (COSPAN k) where
  type CS a ** CS b = CS (a || b)
  type Unit = CS InitialObject
  withOb2 @(CS a) @(CS b) r = withObCoprod @k @a @b r
  leftUnitor = arr leftUnitorCoprod
  leftUnitorInv = arr leftUnitorCoprodInv
  rightUnitor = arr rightUnitorCoprod
  rightUnitorInv = arr rightUnitorCoprodInv
  associator @(CS a) @(CS b) @(CS c) = arr (associatorCoprod @a @b @c)
  associatorInv @(CS a) @(CS b) @(CS c) = arr (associatorCoprodInv @a @b @c)
instance (HasPushouts k) => SymMonoidal (COSPAN k) where
  swap @(CS a) @(CS b) = arr (swapCoprod @a @b)

instance (HasPushouts k, Ob a) => Monoid (CS (a :: k)) where
  mempty = arr initiate
  mappend = arr (id ||| id)
instance (HasPushouts k, Ob a) => Comonoid (CS (a :: k)) where
  counit = coarr initiate
  comult = coarr (id ||| id)
instance (HasPushouts k, Ob a) => Frobenius (CS (a :: k)) where
  spider @x @y = spiderDefault @x @y @(CS a)
instance (HasPushouts k) => Hypergraph (COSPAN k)
instance (HasPushouts k) => CopyDiscard (COSPAN k)

instance (HasPushouts k) => Closed (COSPAN k) where
  type a ~~> b = ExpHG a b
  withObExp @(CS a) @(CS b) r = withObCoprod @k @a @b r
  curry @a @b = curryHG @a @b
  apply @b @c = applyHG @b @c

instance (HasPushouts k) => StarAutonomous (COSPAN k) where
  type Dual a = a
  dual (Cospan f g) = Cospan g f
  dualInv (Cospan f g) = Cospan g f
  linDist @(CS a) @(CS b) (Cospan f g) = Cospan (f . lft @k @a @b) (f . rgt @k @a @b ||| g)
  linDistInv @_ @(CS b) @(CS c) (Cospan f g) = Cospan (f ||| g . lft @k @b @c) (g . rgt @k @b @c)
instance (HasPushouts k) => CompactClosed (COSPAN k) where
  distribDual @(CS a) @(CS b) = withObCoprod @k @a @b id
  dualUnit = id

instance (HasPushouts k) => DaggerProfunctor (Cospan :: CAT (COSPAN k)) where
  dagger = dual

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
      union m (i, j) = let ri = find m i; rj = find m j in if ri == rj then m else IM.insert ri rj m
      unionFind = P.foldl union IM.empty (zipWith (\u v -> (toI (Left u), toI (Right v))) f g)
      groups = IM.elems $ P.foldl @[] (\m x -> IM.insertWith (++) (find unionFind x) [x] m) IM.empty [0 .. sizeA + sizeB - 1]
    in
      reifyList groups \vec ->
        let mapA = tabulate @a (\a -> findIndex (P.elem (toI $ Left a)) vec)
            mapB = tabulate @b (\b -> findIndex (P.elem (toI $ Right b)) vec)
        in Cospan (FinSet mapA) (FinSet mapB)

findIndex :: (a -> P.Bool) -> Vec n a -> Fin n
findIndex _ VNil = P.error "unexpected missing element"
findIndex f (a ::: as)
  | f a = FZ
  | P.otherwise = FS $ findIndex f as
