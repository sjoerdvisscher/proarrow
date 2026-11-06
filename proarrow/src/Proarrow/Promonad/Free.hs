{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free promonad on a profunctor, with base morphisms as pure arrows.
module Proarrow.Promonad.Free where

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), arr, lmap, rmap, tgt, (:~>))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Free (HasFree (..), freeComp, freeMap)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)

-- | A chain of @p@s ending in a base morphism, interpreted into any promonad
-- by 'foldFreePromonad'.
type FreePromonad :: CAT k -> CAT k
data FreePromonad p a b where
  Unit :: (a ~> b) -> FreePromonad p a b
  Comp :: p a b -> FreePromonad p b c -> FreePromonad p a c

-- | Embed a generator as a one-step chain.
liftFreePromonad :: (Profunctor p) => p :~> FreePromonad p
liftFreePromonad p = Comp p (Unit (tgt p))

freePromonadAlg :: p :.: FreePromonad p :~> FreePromonad p
freePromonadAlg (p :.: pp) = Comp p pp

foldFreePromonad :: (Promonad q) => p :~> q -> FreePromonad p :~> q
foldFreePromonad _ (Unit f) = arr f
foldFreePromonad n (Comp p (Unit f)) = rmap f (n p)
foldFreePromonad n (Comp p pp) = foldFreePromonad n pp . n p

instance (Profunctor p) => Profunctor (FreePromonad p) where
  dimap l r (Unit f) = Unit (r . f . l)
  dimap l r (Comp p q) = Comp (lmap l p) (rmap r q)
  r \\ (Unit f) = r \\ f
  r \\ Comp p q = r \\ p \\ q

instance (Profunctor p) => Promonad (FreePromonad p) where
  id = Unit id
  p . Unit f = lmap f p
  p . Comp r q = Comp r (p . q)

instance Functor FreePromonad where
  map = freeMap @Promonad

instance Promonad (Star FreePromonad) where
  id = Star (lift @Promonad)
  Star l . Star r = Star (freeComp @Promonad l r)

instance HasFree Promonad where
  type Free Promonad p = FreePromonad p
  lift = Prof liftFreePromonad
  foldMap (Prof n) = Prof (foldFreePromonad n)
