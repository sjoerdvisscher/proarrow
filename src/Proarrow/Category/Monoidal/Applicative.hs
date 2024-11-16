{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Applicative where

import Control.Applicative qualified as P
import Data.Function (($))
import Data.Kind (Constraint)
import Prelude qualified as P

import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), type (+->))
import Proarrow.Functor (FromProfunctor (..), Functor (..), Prelude (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..), HasProducts, diag)
import Proarrow.Object.Terminal (El, terminate)

type Applicative :: forall {j} {k}. (j -> k) -> Constraint
class (HasProducts j, HasProducts k, Functor f) => Applicative (f :: j -> k) where
  pure :: El a -> El (f a)
  liftA2 :: (Ob a, Ob b) => (a && b ~> c) -> f a && f b ~> f c

instance (MonoidalProfunctor (p :: j +-> k), Ob x, Cartesian j, Cartesian k) => Applicative (FromProfunctor p x) where
  pure a () = FromProfunctor $ dimap terminate a par0
  liftA2 abc (FromProfunctor pxa, FromProfunctor pxb) = FromProfunctor $ dimap diag abc (pxa `par` pxb)

instance (P.Applicative f) => Applicative (Prelude f) where
  pure a () = Prelude (P.pure (a ()))
  liftA2 f (Prelude fa, Prelude fb) = Prelude (P.liftA2 (P.curry f) fa fb)

deriving via Prelude ((,) a) instance (P.Monoid a) => Applicative ((,) a)
deriving via Prelude ((->) a) instance Applicative ((->) a)
deriving via Prelude [] instance Applicative []
deriving via Prelude P.Maybe instance Applicative P.Maybe

type Alternative :: forall {j} {k}. (j -> k) -> Constraint
class (HasCoproducts j, Applicative f) => Alternative (f :: j -> k) where
  empty :: (Ob a) => El (f a)
  alt :: (Ob a, Ob b) => (a || b ~> c) -> f a && f b ~> f c

-- TODO: only works without Applicative as superclass of Alternative. This needs Distributive.
-- instance (MonoidalProfunctor (p :: j +-> k), Ob (x :: k), Cocartesian j, Cartesian k) => Alternative (FromProfunctor p x) where
--   empty () = FromProfunctor $ dimap terminate initiate par0
--   alt abc (FromProfunctor pxa, FromProfunctor pxb) = FromProfunctor $ dimap diag abc (pxa `par` pxb)

instance (P.Alternative f) => Alternative (Prelude f) where
  empty () = Prelude P.empty
  alt abc (Prelude fl, Prelude fr) = Prelude (P.fmap abc $ P.fmap P.Left fl P.<|> P.fmap P.Right fr)

deriving via Prelude [] instance Alternative []
