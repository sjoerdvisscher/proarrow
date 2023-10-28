{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Monoid.Applicative where

import Data.Kind (Constraint)
import Data.Function (($))
import Prelude qualified as P
import Control.Applicative qualified as P

import Proarrow.Core (Promonad(..), CategoryOf(..), (//), lmap, Profunctor (..))
import Proarrow.Functor (Functor(..), Prelude (..))
import Proarrow.Object.Terminal (El, terminate)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..), HasCoproducts, CoproductFunctor)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts, ProductFunctor (..))
import Proarrow.Monoid (Monoid(..))
import Proarrow.Profunctor.Day (Day(..), PList (..))
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Object (obj)
import Proarrow.Category.Monoidal (Strictified(..))
import Proarrow.Profunctor.Composition ((:.:) (..))


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
  AsMonoid :: forall f a b. Ob b => { getAsMonoid :: a ~> f b } -> AsMonoid f a b
instance Functor f => Profunctor (AsMonoid f) where
  dimap l r (AsMonoid g) = AsMonoid (map r . g . l) \\ r
  r \\ AsMonoid f = r \\ f

instance (HasProducts j, HasProducts k, Applicative f) => Monoid (Day (Strictified ProductFunctor) (Strictified ProductFunctor)) (AsMonoid (f :: j -> k)) where
  mempty = Day \PNil -> Strictified id :.: PCons (AsMonoid (pure @f id)) PNil :.: Strictified id
  mappend = Day \(AsMonoid @_ @a1 @b1 f `PCons` (AsMonoid @_ @a2 @b2 g `PCons` PNil)) ->
    f // g // let a12 = obj @a1 *** obj @a2; b12 = obj @b1 *** obj @b2
    in Strictified a12 :.: PCons (AsMonoid (liftA2 @f @b1 @b2 b12 . (f *** g))) PNil :.: Strictified b12 \\ a12 \\ b12

instance (HasCoproducts j, HasProducts k, Alternative f) => Monoid (Day (Strictified ProductFunctor) (Strictified CoproductFunctor)) (AsMonoid (f :: j -> k)) where
  mempty = Day \PNil -> Strictified id :.: PCons (AsMonoid empty) PNil :.: Strictified id
  mappend = Day \(AsMonoid @_ @a1 @b1 f `PCons` (AsMonoid @_ @a2 @b2 g `PCons` PNil)) ->
    f // g // let a12 = obj @a1 *** obj @a2; b12 = obj @b1 +++ obj @b2
    in Strictified a12 :.: PCons (AsMonoid (alt @f @b1 @b2 b12 . (f *** g))) PNil :.: Strictified b12 \\ a12 \\ b12


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