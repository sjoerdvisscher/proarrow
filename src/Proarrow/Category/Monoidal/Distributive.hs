{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Distributive where

import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Prelude (Either (..), const)
import Prelude qualified as P

import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..))
import Proarrow.Object.BinaryCoproduct (Coprod (..), HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Object.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Object.Exponential (BiCCC)
import Proarrow.Helper.CCC
import Proarrow.Object.Initial (HasInitialObject (..))

class (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p
instance (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p

copar0 :: (DistributiveProfunctor p) => p InitialObject InitialObject
copar0 = unCoprod par0

copar :: (DistributiveProfunctor p) => p a b -> p c d -> p (a || c) (b || d)
copar p q = unCoprod (Coprod p `par` Coprod q)

class (Monoidal k, HasCoproducts k, DistributiveProfunctor ((~>) :: CAT k)) => Distributive k where
  distL :: (Ob (a :: k), Ob b, Ob c) => (a ** (b || c)) ~> (a ** b || a ** c)
  distR :: (Ob (a :: k), Ob b, Ob c) => ((a || b) ** c) ~> (a ** c || b ** c)
  distL0 :: (Ob (a :: k)) => (a ** InitialObject) ~> InitialObject
  distR0 :: (Ob (a :: k)) => (InitialObject ** a) ~> InitialObject

instance Distributive Type where
  distL (a, e) = bimap (a,) (a,) e
  distR (e, c) = bimap (,c) (,c) e
  distL0 = P.snd
  distR0 = P.fst

instance Distributive () where
  distL = U.Unit
  distR = U.Unit
  distL0 = U.Unit
  distR0 = U.Unit

instance (BiCCC k) => Distributive (PROD k) where
  distL @(PR a) @(PR b) @(PR c) =
    Prod
      ( toCCC @(F a * (F b + F c)) @((F a * F b) + (F a * F c))
          (lam \(a :& bc) -> either (lam \b -> lam \a' -> left (a' :& b)) (lam \c -> lam \a' -> right (a' :& c)) $ bc $ a)
      )
  distR @(PR a) @(PR b) @(PR c) =
    Prod
      ( toCCC @((F a + F b) * F c) @((F a * F c) + (F b * F c))
          (lam \(ab :& c) -> either (lam \a -> lam \c' -> left (a :& c')) (lam \b -> lam \c' -> right (b :& c')) $ ab $ c)
      )
  distL0 @(PR a) = Prod (toCCC @(F a * InitF) @InitF (lam \(_ :& v) -> v))
  distR0 @(PR a) = Prod (toCCC @(InitF * F a) @InitF (lam \(v :& _) -> v))

travList :: (DistributiveProfunctor p) => p a b -> p [a] [b]
travList p = go
  where
    go =
      dimap
        (\l -> case l of [] -> Left (); (x : xs) -> Right (x, xs))
        (const [] ||| \(x, xs) -> x : xs)
        (par0 `copar` (p `par` go))