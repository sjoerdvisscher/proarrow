{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Distributive where

import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Prelude (Either (..), const)
import Prelude qualified as P

import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), lmap, src, (:~>), type (+->))
import Proarrow.Helper.CCC
import Proarrow.Object.BinaryCoproduct (Coprod (..), HasBinaryCoproducts (..), HasCoproducts, copar)
import Proarrow.Object.BinaryProduct (Cartesian, fst', snd', PROD (..), Prod (..), diag)
import Proarrow.Object.Exponential (BiCCC)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Product ((:*:) (..))
import Proarrow.Profunctor.Star (Star (..))

class (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p
instance (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p

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

class (Profunctor t) => Traversable t where
  traverse :: (DistributiveProfunctor p) => t :.: p :~> p :.: t

instance (CategoryOf k) => Traversable (Id :: k +-> k) where
  traverse (Id f :.: p) = lmap f p :.: Id id \\ p

instance Traversable (->) where
  traverse (f :.: p) = lmap f p :.: id

instance (Traversable p, Traversable q) => Traversable (p :.: q) where
  traverse ((p :.: q) :.: r) = case traverse (q :.: r) of
    r' :.: q' -> case traverse (p :.: r') of
      r'' :.: p' -> r'' :.: (p' :.: q')

instance (Cartesian k, Traversable p, Traversable q) => Traversable ((p :: k +-> k) :*: q) where
  traverse ((p :*: q) :.: r) = case (traverse (p :.: r), traverse (q :.: r)) of
    (r' :.: p', r'' :.: q') -> lmap diag (r' `par` r'') :.: (lmap (fst' (src p') (src q')) p' :*: lmap (snd' (src p') (src q')) q') \\ p

instance (Traversable p, Traversable q) => Traversable (p :+: q) where
  traverse (InjL p :.: r) = case traverse (p :.: r) of r' :.: p' -> r' :.: InjL p'
  traverse (InjR q :.: r) = case traverse (q :.: r) of r' :.: q' -> r' :.: InjR q'

instance Traversable (Star P.Maybe) where
  traverse (Star a2mb :.: p) = lmap a2mb go :.: Star P.id
    where
      go =
        dimap
          (P.maybe (Left ()) Right)
          (const P.Nothing ||| P.Just)
          (par0 `copar` p)

instance Traversable (Star []) where
  traverse (Star a2bs :.: p) = lmap a2bs go :.: Star P.id
    where
      go =
        dimap
          (\l -> case l of [] -> Left (); (x : xs) -> Right (x, xs))
          (const [] ||| \(x, xs) -> x : xs)
          (par0 `copar` (p `par` go))
