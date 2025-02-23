{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Action where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj, type (+->))

-- | Weighted strength for a monoidal action. Usually this is used unweighted, where @w@ is the hom profunctor.
type Strong :: forall {j} {k}. Kind -> j +-> k -> Constraint
class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Strong m (p :: c +-> d) where
  act :: forall (a :: m) b x y. a ~> b -> p x y -> p (Act a x) (Act b y)

class (Monoidal m, CategoryOf k, Strong m ((~>) :: CAT k)) => MonoidalAction m k where
  -- I would like to default Act to `**`, but that doesn't seem possible without GHC thinking `m` and `k` are the same.
  type Act (a :: m) (x :: k) :: k
  unitor :: (Ob (x :: k)) => Act (Unit :: m) x ~> x
  unitorInv :: (Ob (x :: k)) => x ~> Act (Unit :: m) x
  multiplicator :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act a (Act b x) ~> Act (a ** b) x
  multiplicatorInv :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act (a ** b) x ~> Act a (Act b x)

class (Act a b ~ a ** b) => ActIsTensor a b
instance (Act a b ~ a ** b) => ActIsTensor a b
class (Act a (Act b c) ~ a ** (b ** c), a ** (Act b c) ~ a ** (b ** c), Act a (b ** c) ~ a ** (b ** c)) => ActIsTensor3 a b c
instance (Act a (Act b c) ~ a ** (b ** c), a ** (Act b c) ~ a ** (b ** c), Act a (b ** c) ~ a ** (b ** c)) => ActIsTensor3 a b c
class (MonoidalAction k k, forall (a :: k) (b :: k). ActIsTensor a b, forall (a :: k) (b :: k) (c :: k). ActIsTensor3 a b c) => SelfAction k
instance (MonoidalAction k k, forall (a :: k) (b :: k). ActIsTensor a b, forall (a :: k) (b :: k) (c :: k). ActIsTensor3 a b c) => SelfAction k

composeActs
  :: forall {m} {k} (x :: m) y (c :: k) a b
   . (MonoidalAction m k, Ob x, Ob y, Ob c)
  => a ~> Act x b
  -> b ~> Act y c
  -> a ~> Act (x ** y) c
composeActs f g = multiplicator @m @k @x @y @c . act (obj @x) g . f

decomposeActs
  :: forall {m} {k} (x :: m) y (c :: k) a b
   . (MonoidalAction m k, Ob x, Ob y, Ob c)
  => Act y c ~> b
  -> Act x b ~> a
  -> Act (x ** y) c ~> a
decomposeActs f g = g . act (obj @x) f . multiplicatorInv @m @k @x @y @c
