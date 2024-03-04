{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Monoidal.Applicative where

import Data.Kind (Constraint)
import Data.Function (($))
import Prelude qualified as P
import Control.Applicative qualified as P

import Proarrow.Core (Promonad(..), CategoryOf(..), (//), lmap, Profunctor (..), PRO, obj)
import Proarrow.Functor (Functor(..), Prelude (..))
import Proarrow.Object.Terminal (El, terminate)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..), HasCoproducts, COPROD (..), Coprod (..), lft, rgt)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD (..), Prod (..), fst, snd)
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))


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


class Profunctor p => Proapplicative p where
  pureP :: Ob a => El b -> p a b
  apP :: p a b -> p a c -> p a (b && c)

instance Applicative f => Proapplicative (Star f) where
  pureP b = b // Star (lmap terminate (pure b))
  apP (Star @b f) (Star @c g) =
    let bc = obj @b *** obj @c
    in bc // Star (liftA2 @f @b @c bc . (f &&& g))

type App :: PRO j k -> PRO (PROD j) (PROD k)
data App p a b where
  App :: p a b -> App p (PR a) (PR b)
instance Profunctor p => Profunctor (App p) where
  dimap (Prod l) (Prod r) (App p) = App (dimap l r p)
  r \\ App p = r \\ p
instance (HasProducts j, HasProducts k, Proapplicative p) => MonoidalProfunctor (App (p :: PRO j k)) where
  lift0 = App (pureP id)
  lift2 (App @_ @a1 p) (App @_ @a2 q) = App (apP (lmap (fst @a1 @a2) p) (lmap (snd @a1 @a2) q)) \\ p \\ q



type Alternative :: forall {j} {k}. (j -> k) -> Constraint
class (HasCoproducts j, Applicative f) => Alternative (f :: j -> k) where
  empty :: El (f a)
  alt :: (a || b ~> c) -> f a && f b ~> f c

instance P.Alternative f => Alternative (Prelude f) where
  empty () = Prelude P.empty
  alt abc (Prelude fl, Prelude fr) = Prelude (P.fmap abc $ P.fmap P.Left fl P.<|> P.fmap P.Right fr)


class Proapplicative p => Proalternative p where
  emptyP :: (Ob a, Ob b) => p a b
  altP :: p a b -> p a b -> p a b

instance Alternative f => Proalternative (Star f) where
  emptyP = Star (empty . terminate)
  altP (Star @b f) (Star g) =
    let bb = obj @b ||| obj @b
    in bb // Star (alt @f @b @b bb . (f &&& g))

type Alt :: PRO j k -> PRO (PROD j) (COPROD k)
data Alt p a b where
  Alt :: p a b -> Alt p (PR a) (COPR b)
instance Profunctor p => Profunctor (Alt p) where
  dimap (Prod l) (Coprod r) (Alt p) = Alt (dimap l r p)
  r \\ Alt p = r \\ p
instance (HasProducts j, HasCoproducts k, Proalternative p) => MonoidalProfunctor (Alt (p :: PRO j k)) where
  lift0 = Alt emptyP
  lift2 (Alt @_ @a1 @b1 p) (Alt @_ @a2 @b2 q) = Alt (altP (dimap (fst @a1 @a2) (lft @b1 @b2) p) (dimap (snd @a1 @a2) (rgt @b1 @b2) q)) \\ p \\ q
