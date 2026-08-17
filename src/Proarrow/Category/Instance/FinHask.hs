{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.FinHask where

import Data.Coerce qualified as P
import Data.Containers.ListUtils (nubOrd)
import Data.Data (Proxy (..))
import Data.Kind (Type)
import Data.List (genericLength)
import Data.List qualified as P
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Universe.Class (Finite (..), Universe (..))
import Data.Universe.Helpers (Tagged (..), retag)
import Data.Void (Void)
import GHC.TypeNats (KnownNat, Nat, natVal, withKnownNat, withSomeSNat)
import Prelude (Bool (..), ($))
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Distributive (Distributive (..), distLProd, distRProd)
import Proarrow.Category.Topos (ElementaryTopos, HasEpiMonoFactorization (..), HasSubobjectClassifier (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..), pushoutDefault)
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Limit.BinaryProduct
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
import Proarrow.Limit.Equalizer (HasEqualizers (..), pullbackDefault)
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))

newtype Fin (n :: Nat) = Fin {unFin :: P.Int}
  deriving newtype (P.Eq, P.Ord, P.Show, P.Num)

instance (KnownNat n) => Universe (Fin n) where
  universe = P.coerce @[P.Int] [0 .. (P.fromIntegral (natVal (Proxy @n)) P.- 1)]

instance (KnownNat n) => Finite (Fin n) where
  cardinality = Tagged (natVal (Proxy @n))

type data FINHASK = FH Type

type FinHask :: CAT FINHASK
data FinHask a b where
  FinHask :: (Ob (FH a), Ob (FH b)) => {unFinHask :: Map a b} -> FinHask (FH a) (FH b)

instance P.Show (FinHask a b) where
  show (FinHask m) = P.show m
deriving instance P.Eq (FinHask a b)
deriving instance P.Ord (FinHask a b)
instance (Ob a, Ob b) => Universe (FinHask a b) where
  universe = fromList P.<$> P.traverse (\a -> (a,) P.<$> universe) universe
instance (Ob a, Ob b) => Finite (FinHask a b) where
  cardinality =
    P.liftA2
      (P.^)
      (retag @_ @_ @(FinHask a b) (cardinality @(UN FH b)))
      (retag @_ @_ @(FinHask a b) (cardinality @(UN FH a)))

(!) :: (P.Ord (UN FH a)) => FinHask a b -> UN FH a -> UN FH b
FinHask m ! a = case M.lookup a m of
  P.Just x -> x
  P.Nothing -> P.error $ "Index " P.++ P.show a P.++ " out of bounds for " P.++ P.show m

arr :: (Ob (FH a), Ob (FH b)) => (a -> b) -> FinHask (FH a) (FH b)
arr f = fromList [(x, f x) | x <- universeF]

reifyList :: [a] -> (forall l. (Ob (FH l)) => Map l a -> r) -> r
reifyList xs k =
  withSomeSNat (genericLength xs) \ @n snat ->
    withKnownNat snat (k @(Fin n) (M.fromList (P.zip universeF xs)))

fromList :: (Ob (FH a), Ob (FH b)) => [(a, b)] -> FinHask (FH a) (FH b)
fromList = FinHask . M.fromList

toList :: (Ob (FH a), Ob (FH b)) => FinHask (FH a) (FH b) -> [(a, b)]
toList (FinHask m) = M.toList m

instance Profunctor FinHask where
  dimap = dimapDefault
  r \\ FinHask{} = r
instance Promonad FinHask where
  id = arr id
  FinHask l . FinHask r = FinHask (P.fmap (l M.!) r)
instance CategoryOf FINHASK where
  type (~>) = FinHask
  type Ob a = (Is FH a, Finite (UN FH a), P.Ord (UN FH a), P.Show (UN FH a))

instance HasInitialObject FINHASK where
  type InitialObject = FH Void
  initiate = FinHask M.empty
instance HasBinaryCoproducts FINHASK where
  type FH a || FH b = FH (P.Either a b)
  withObCoprod r = r
  lft = arr P.Left
  rgt = arr P.Right
  FinHask l ||| FinHask r = FinHask (M.mapKeys P.Left l P.<> M.mapKeys P.Right r)

instance HasTerminalObject FINHASK where
  type TerminalObject = FH ()
  terminate = arr \_ -> ()
instance HasBinaryProducts FINHASK where
  type FH a && FH b = FH (a, b)
  withObProd r = r
  fst = arr P.fst
  snd = arr P.snd
  FinHask l &&& FinHask r =
    FinHask
      ( M.mergeWithKey
          (\_ a b -> P.Just (a, b))
          (\_ -> M.empty)
          (\_ -> M.empty)
          l
          r
      )

instance MonoidalProfunctor FinHask where
  one = id
  (**) = (***)

instance Monoidal FINHASK where
  type a ** b = a && b
  type Unit = TerminalObject
  withOb2 @a @b = withObProd @_ @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @a @b @c = associatorProd @a @b @c
  associatorInv @a @b @c = associatorProdInv @a @b @c

instance SymMonoidal FINHASK where
  swap @a @b = swapProd @a @b

instance Closed FINHASK where
  type a ~~> b = FH (FinHask a b)
  withObExp r = r
  curry f@FinHask{} = arr \a -> arr \b -> f ! (a, b)
  apply = arr \(m, x) -> m ! x

instance Distributive FINHASK where
  distL @a @b @c = distLProd @a @b @c
  distR @a @b @c = distRProd @a @b @c
  absorbL = FinHask M.empty
  absorbR = FinHask M.empty

instance (Ob (FH a)) => Comonoid (FH a) where
  counit = terminate
  comult = diag

instance CopyDiscard FINHASK

instance Monoid (FH ()) where
  mempty = terminate
  mappend = terminate

-- | >>> let f :: FinHask (FH (Fin 4)) (FH (Fin 3)) = fromList [(0,0), (1,1), (2,1), (3,0)]
-- >>> let g :: FinHask (FH (Fin 4)) (FH (Fin 3)) = fromList [(0,2), (1,0), (2,1), (3,0)]
-- >>> let h :: FinHask (FH (Fin 3)) (FH (Fin 4)) = fromList [(0,3), (1,2), (2,3)]
-- >>> (case factorEqualizer f g h of p :.: q -> P.show (p, q, q . p)) :: P.String
-- "(fromList [(0,1),(1,0),(2,1)],fromList [(0,2),(1,3)],fromList [(0,3),(1,2),(2,3)])"

instance HasEqualizers FINHASK where
  factorEqualizer f@FinHask{} g (FinHask h) =
    let groups = [x | x <- universeF, f ! x P.== g ! x]
    in reifyList groups \e ->
         let invE = M.fromList [(FinHask e ! b, b) | b <- universeF]
         in FinHask ((invE M.!) P.<$> h) :.: FinHask e

-- | Example 3.84 of Seven Sketches (A: 0=red, 1=blue, 2=black)
-- >>> data Color = Red | Blue | Black deriving (P.Eq, P.Ord, P.Show, P.Enum, P.Bounded, Universe, Finite)
-- >>> let f :: FinHask (FH (Fin 6)) (FH Color) = fromList [(0,Red), (1,Blue), (2,Red), (3,Red), (4,Black), (5,Blue)]
-- >>> let g :: FinHask (FH (Fin 4)) (FH Color) = fromList [(0,Black), (1,Red), (2,Blue), (3,Red)]
-- >>> (pullback f g \(FinHask l) (FinHask r) -> P.show (P.zip (M.elems l) (M.elems r))) :: P.String
-- "[(0,1),(0,3),(1,2),(2,1),(2,3),(3,1),(3,3),(4,0),(5,2)]"
instance HasPullbacks FINHASK where
  pullback = pullbackDefault

instance HasCoequalizers FINHASK where
  factorCoequalizer (FinHask @_ @b f) (FinHask g) (FinHask h) =
    let
      find m i = P.maybe i (find m) $ M.lookup i m
      union m (i, j) = let ri = find m i; rj = find m j in if ri P.== rj then m else M.insert ri rj m
      unionFind = P.foldl union M.empty (P.zip (M.elems f) (M.elems g))
      step m x = M.insertWith (P.++) (find unionFind x) [x] m
      groups = M.elems $ P.foldl step M.empty (universeF @b)
    in
      reifyList groups \ce ->
        let invMap = M.fromList $ P.concatMap (\(l, bs) -> P.map (,l) bs) $ M.toList ce
        in FinHask invMap :.: FinHask (((h M.!) . (P.!! 0)) P.<$> ce)

-- | Exercise 6.22 of Seven Sketches
-- >>> let l :: FinHask (FH (Fin 4)) (FH (Fin 3)) = fromList [(0,0), (1,0), (2,1), (3,2)]
-- >>> let r :: FinHask (FH (Fin 4)) (FH (Fin 5)) = fromList [(0,0), (1,2), (2,4), (3,4)]
-- >>> (pushout l r \l' r' -> P.show (l', r')) :: P.String
-- "(fromList [(0,1),(1,3),(2,3)],fromList [(0,1),(1,0),(2,1),(3,2),(4,3)])"
instance HasPushouts FINHASK where
  pushout = pushoutDefault

-- | >>> import Proarrow.Colimit.Pushout (isEpi)
-- >>> let f :: FinHask (FH (Fin 3)) (FH (Fin 3)) = fromList [(0,2), (1,0), (2,1)]
-- >>> (pushout f f \(FinHask g1) (FinHask g2) -> P.show (g1, g2)) :: P.String
-- "(fromList [(0,0),(1,1),(2,2)],fromList [(0,0),(1,1),(2,2)])"
-- >>> isEpi (f :: FinHask (FH (Fin 3)) (FH (Fin 3)))
-- True
-- >>> import Proarrow.Limit.Pullback (isMono)
-- >>> (pullback f f \(FinHask l) (FinHask r) -> P.show (l, r)) :: P.String
-- "(fromList [(0,0),(1,1),(2,2)],fromList [(0,0),(1,1),(2,2)])"
-- >>> isMono f
-- True
-- >>> import Proarrow.Category.Topos (classifyImage, classifyKernelPair, and, or, implies, false)
-- >>> (case factorize f of p :.: q -> P.show (p, q) \\ p \\ q) :: P.String
-- "(fromList [(0,0),(1,1),(2,2)],fromList [(0,2),(1,0),(2,1)])"
-- >>> (classifyImage f, classifyKernelPair f)
-- (fromList [(0,True),(1,True),(2,True)],fromList [((0,0),True),((0,1),False),((0,2),False),((1,0),False),((1,1),True),((1,2),False),((2,0),False),((2,1),False),((2,2),True)])
-- >>> [and, or, implies] :: [FinHask (FH (Bool, Bool)) (FH Bool)]
-- [fromList [((False,False),False),((False,True),False),((True,False),False),((True,True),True)],fromList [((False,False),False),((False,True),True),((True,False),True),((True,True),True)],fromList [((False,False),True),((False,True),True),((True,False),False),((True,True),True)]]
-- >>> false :: FinHask (FH ()) (FH Bool)
-- fromList [((),False)]

instance HasSubobjectClassifier FINHASK where
  type Omega = FH Bool
  true = arr \_ -> True
  classifyGraph f@FinHask{} = arr \(a, b) -> f ! a P.== b

instance HasEpiMonoFactorization FINHASK where
  factorize (FinHask f) = reifyList (nubOrd (M.elems f)) \lb ->
    let invMap = M.fromList [(lb M.! l, l) | l <- universeF]
    in FinHask (P.fmap (invMap M.!) f) :.: FinHask lb

instance ElementaryTopos FINHASK
