{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal.Action where

import Data.Kind (Constraint)

import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad(..), type (+->), obj)

-- | Weighted strength for a monoidal action. Usually this is used unweighted, where @w@ is an arrow.
type Strong :: forall {m} {m'} {j} {k}. m +-> m' -> j +-> k -> Constraint
class (MonoidalAction m c, MonoidalAction m' d, Profunctor p) => Strong (w :: m +-> m') (p :: c +-> d) where
  act :: w a b -> p x y -> p (Act a x) (Act b y)

class (Monoidal m, CategoryOf k, Strong ((~>) :: CAT m) ((~>) :: CAT k)) => MonoidalAction m k where
  -- I would like to default Act to `**`, but that doesn't seem possible without GHC thinking `m` and `k` are the same.
  type Act (a :: m) (x :: k) :: k
  unitor :: (Ob (x :: k)) => Act (Unit :: m) x ~> x
  unitorInv :: (Ob (x :: k)) => x ~> Act (Unit :: m) x
  multiplicator :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act a (Act b x) ~> Act (a ** b) x
  multiplicatorInv :: (Ob (a :: m), Ob (b :: m), Ob (x :: k)) => Act (a ** b) x ~> Act a (Act b x)

composeActs :: forall {m} {k} (x :: m) y (c :: k) a b. (MonoidalAction m k, Ob x, Ob y, Ob c) => a ~> Act x b -> b ~> Act y c -> a ~> Act (x ** y) c
composeActs f g = multiplicator @m @k @x @y @c . act (obj @x) g . f

decomposeActs :: forall {m} {k} (x :: m) y (c :: k) a b. (MonoidalAction m k, Ob x, Ob y, Ob c) => Act y c ~> b -> Act x b ~> a -> Act (x ** y) c ~> a
decomposeActs f g = g . act (obj @x) f . multiplicatorInv @m @k @x @y @c
