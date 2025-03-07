{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Applicative where

import Control.Applicative qualified as P
import Data.Function (($))
import Data.Kind (Constraint)
import Data.List.NonEmpty qualified as P
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Distributive (Distributive)
import Proarrow.Core (CategoryOf (..), Profunctor (..), type (+->))
import Proarrow.Functor (FromProfunctor (..), Functor (..), Prelude (..))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))

type Applicative :: forall {j} {k}. (j -> k) -> Constraint
class (Monoidal j, Monoidal k, Functor f) => Applicative (f :: j -> k) where
  pure :: Unit ~> a -> Unit ~> f a
  liftA2 :: (Ob a, Ob b) => (a ** b ~> c) -> f a ** f b ~> f c

instance (MonoidalProfunctor (p :: j +-> k), Comonoid x) => Applicative (FromProfunctor p x) where
  pure a () = FromProfunctor $ dimap counit a par0
  liftA2 abc (FromProfunctor pxa, FromProfunctor pxb) = FromProfunctor $ dimap comult abc (pxa `par` pxb)

instance (P.Applicative f) => Applicative (Prelude f) where
  pure a () = Prelude (P.pure (a ()))
  liftA2 f (Prelude fa, Prelude fb) = Prelude (P.liftA2 (P.curry f) fa fb)

deriving via Prelude ((,) a) instance (P.Monoid a) => Applicative ((,) a)
deriving via Prelude ((->) a) instance Applicative ((->) a)
deriving via Prelude [] instance Applicative []
deriving via Prelude (P.Either e) instance Applicative (P.Either e)
deriving via Prelude P.IO instance Applicative P.IO
deriving via Prelude P.Maybe instance Applicative P.Maybe
deriving via Prelude P.NonEmpty instance Applicative P.NonEmpty

type Alternative :: forall {j} {k}. (j -> k) -> Constraint
class (Distributive j, Applicative f) => Alternative (f :: j -> k) where
  empty :: (Ob a) => Unit ~> f a
  alt :: (Ob a, Ob b) => (a || b ~> c) -> f a ** f b ~> f c

instance (P.Alternative f) => Alternative (Prelude f) where
  empty () = Prelude P.empty
  alt abc (Prelude fl, Prelude fr) = Prelude (P.fmap abc $ P.fmap P.Left fl P.<|> P.fmap P.Right fr)

deriving via Prelude [] instance Alternative []
deriving via Prelude P.Maybe instance Alternative P.Maybe
deriving via Prelude P.IO instance Alternative P.IO
