{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Monoid.Applicative where

import Data.Kind (Constraint)
import Data.Function (($))
import Prelude qualified as P
import Control.Applicative qualified as P

import Proarrow.Core (Promonad(..), CategoryOf(..), (//), lmap, Profunctor (..), UN)
import Proarrow.Functor (Functor(..), Prelude (..))
import Proarrow.Object.Terminal (El, terminate)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..), HasCoproducts, COPROD (..), Coprod (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD (..), Prod (..))
import Proarrow.Monoid (Monoid(..))
import Proarrow.Profunctor.Day (Day(..), DayUnit(..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Object (obj)
import Proarrow.Category.Instance.Prof (Prof(..))


type Applicative :: forall {j} {k}. (j -> k) -> Constraint
class (HasProducts j, HasProducts k, Functor f) => Applicative (f :: j -> k) where
  pure :: El a -> El (f a)
  liftA2 :: (a && b ~> c) -> f a && f b ~> f c

instance P.Applicative f => Applicative (Prelude f) where
  pure a () = Prelude (P.pure (a ()))
  liftA2 f (Prelude fa, Prelude fb) = Prelude (P.liftA2 (P.curry f) fa fb)

deriving via Prelude ((,) a) instance P.Monoid a => Applicative ((,) a)
deriving via Prelude ((->) a) instance Applicative ((->) a)
deriving via Prelude [] instance Applicative []

type Alternative :: forall {j} {k}. (j -> k) -> Constraint
class (HasCoproducts j, Applicative f) => Alternative (f :: j -> k) where
  empty :: El (f a)
  alt :: (a || b ~> c) -> f a && f b ~> f c

instance P.Alternative f => Alternative (Prelude f) where
  empty () = Prelude P.empty
  alt abc (Prelude fl, Prelude fr) = Prelude (P.fmap abc $ P.fmap P.Left fl P.<|> P.fmap P.Right fr)

data AsMonoid f a b where
  AsMonoid :: forall {j} {k} (f :: j -> k) a b. (Ob a, Ob b) => UN PR a ~> f (UN PR b) -> AsMonoid f a b
instance Functor f => Profunctor (AsMonoid f) where
  dimap (Prod l) (Prod r) (AsMonoid g) = AsMonoid (map r . g . l) \\ r \\ l
  r \\ AsMonoid f = r \\ f

instance (HasProducts j, HasProducts k, Applicative f) => Monoid (AsMonoid (f :: j -> k)) where
  mempty = Prof \(DayUnit (Prod f) (Prod g)) -> AsMonoid (pure @f g . f) \\ f \\ g
  mappend = Prof \(Day (Prod f) (AsMonoid @_ @_ @x p) (AsMonoid @_ @_ @y q) (Prod g)) -> AsMonoid (liftA2 @f @(UN PR x) @(UN PR y) g . (p *** q) . f)

data AsMonoidAlt f a b where
  AsMonoidAlt :: forall {j} {k} (f :: j -> k) a b. (Ob a, Ob b) => UN PR a ~> f (UN COPR b) -> AsMonoidAlt f a b
instance Functor f => Profunctor (AsMonoidAlt f) where
  dimap (Prod l) (Coprod r) (AsMonoidAlt g) = AsMonoidAlt (map r . g . l) \\ r \\ l
  r \\ AsMonoidAlt f = r \\ f

instance (HasCoproducts j, HasProducts k, Alternative f) => Monoid (AsMonoidAlt (f :: j -> k)) where
  mempty = Prof \(DayUnit (Prod f) (Coprod g)) -> AsMonoidAlt (empty @f . f) \\ f \\ g
  mappend = Prof \(Day (Prod f) (AsMonoidAlt @_ @_ @x p) (AsMonoidAlt @_ @_ @y q) (Coprod g)) -> AsMonoidAlt (alt @f @(UN COPR x) @(UN COPR y) g . (p *** q) . f)


class Profunctor p => Proapplicative p where
  pureP :: Ob a => El b -> p a b
  apP :: p a b -> p a c -> p a (b && c)

instance Applicative f => Proapplicative (Star f) where
  pureP b = b // Star (lmap terminate (pure b))
  apP (Star @b f) (Star @c g) =
    let bc = obj @b *** obj @c
    in bc // Star (liftA2 @f @b @c bc . (f &&& g))

class Proapplicative p => Proalternative p where
  emptyP :: (Ob a, Ob b) => p a b
  altP :: p a b -> p a b -> p a b

instance Alternative f => Proalternative (Star f) where
  emptyP = Star (empty . terminate)
  altP (Star @b f) (Star g) =
    let bb = obj @b ||| obj @b
    in bb // Star (alt @f @b @b bb . (f &&& g))