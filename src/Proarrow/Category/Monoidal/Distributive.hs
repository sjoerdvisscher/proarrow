{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Distributive where

import Data.Bifunctor (bimap)
import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (SelfAction, Strong (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Profunctor (..)
  , Promonad (..)
  , lmap
  , rmap
  , src
  , tgt
  , (:~>)
  , type (+->)
  )
import Proarrow.Helper.CCC
import Proarrow.Object.BinaryCoproduct (Coprod (..), HasBinaryCoproducts (..), HasCoproducts, codiag, copar, lft', rgt')
import Proarrow.Object.BinaryProduct (Cartesian, PROD (..), Prod (..), diag, fst', snd', HasBinaryProducts (..))
import Proarrow.Object.Exponential (BiCCC)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Product ((:*:) (..))

class (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p
instance (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p

class (Monoidal k, HasCoproducts k, DistributiveProfunctor (Id :: CAT k)) => Distributive k where
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
  distL @(PR a) @(PR b) @(PR c) = Prod (distLProd @a @b @c)
  distR @(PR a) @(PR b) @(PR c) = Prod (distRProd @a @b @c)
  distL0 @(PR a) = Prod (toCCC @(F a * InitF) @InitF (lam \(_ :& v) -> v))
  distR0 @(PR a) = Prod (toCCC @(InitF * F a) @InitF (lam \(v :& _) -> v))

distLProd :: forall {k} (a :: k) (b :: k) (c :: k). (BiCCC k, Ob a, Ob b, Ob c) => (a && (b || c)) ~> (a && b || a && c)
distLProd = toCCC @(F a * (F b + F c)) @((F a * F b) + (F a * F c))
  (lam \(a :& bc) -> either (lam \b -> lam \a' -> left (a' :& b)) (lam \c -> lam \a' -> right (a' :& c)) $ bc $ a)

distRProd :: forall {k} (a :: k) (b :: k) (c :: k). (BiCCC k, Ob a, Ob b, Ob c) => ((a || b) && c) ~> (a && c || b && c)
distRProd = toCCC @((F a + F b) * F c) @((F a * F c) + (F b * F c))
  (lam \(ab :& c) -> either (lam \a -> lam \c' -> left (a :& c')) (lam \b -> lam \c' -> right (b :& c')) $ ab $ c)

type Traversable :: forall {k}. (k +-> k) -> Constraint
class (Profunctor t) => Traversable (t :: k +-> k) where
  traverse :: (DistributiveProfunctor (p :: k +-> k), Strong k p, SelfAction k) => t :.: p :~> p :.: t

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

type Cotraversable :: forall {k}. (k +-> k) -> Constraint
class (Profunctor t) => Cotraversable (t :: k +-> k) where
  cotraverse :: (DistributiveProfunctor (p :: k +-> k), Strong k p, SelfAction k) => p :.: t :~> t :.: p

instance (CategoryOf k) => Cotraversable (Id :: k +-> k) where
  cotraverse (p :.: Id f) = Id id :.: rmap f p \\ p

instance Cotraversable (->) where
  cotraverse (p :.: f) = id :.: rmap f p

instance (Cotraversable p, Cotraversable q) => Cotraversable (p :.: q) where
  cotraverse (r :.: (p :.: q)) = case cotraverse (r :.: p) of
    p' :.: r' -> case cotraverse (r' :.: q) of
      q' :.: r'' -> (p' :.: q') :.: r''

instance (HasBinaryCoproducts k, Cotraversable p, Cotraversable q) => Cotraversable ((p :: k +-> k) :*: q) where
  cotraverse (r :.: (p :*: q)) = case (cotraverse (r :.: p), cotraverse (r :.: q)) of
    (p' :.: r', q' :.: r'') -> (rmap (lft' (tgt p') (tgt q')) p' :*: rmap (rgt' (tgt p') (tgt q')) q') :.: rmap codiag (r' `copar` r'') \\ p

instance (Cotraversable p, Cotraversable q) => Cotraversable (p :+: q) where
  cotraverse (r :.: InjL p) = case cotraverse (r :.: p) of p' :.: r' -> InjL p' :.: r'
  cotraverse (r :.: InjR q) = case cotraverse (r :.: q) of q' :.: r' -> InjR q' :.: r'
