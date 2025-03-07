module Proarrow.Promonad.State where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), swap')
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj)

data State s a b where
  State :: (Ob a, Ob b) => (s ** a) ~> (s ** b) -> State s a b

instance (Monoidal k, Ob s) => Profunctor (State (s :: k)) where
  dimap l r (State f) = State ((obj @s `par` r) . f . (obj @s `par` l)) \\ l \\ r
  r \\ State f = r \\ f

instance (Monoidal k, Ob s) => Promonad (State (s :: k)) where
  id :: forall a. (Ob a) => State s a a
  id = State (obj @s `par` obj @a)
  State f . State g = State (f . g)

-- | Note: This is only premonoidal, not monoidal.
instance (SymMonoidal k, Ob s) => MonoidalProfunctor (State (s :: k)) where
  par0 = State (obj @s `par` par0) \\ (par0 :: (Unit :: k) ~> Unit)
  par (State @a1 @b1 f) (State @a2 @b2 g) =
    let s = obj @s; a1 = obj @a1; b1 = obj @b1; a2 = obj @a2; b2 = obj @b2
    in State
        ( (s `par` swap' b2 b1)
            . associator @_ @s @b2 @b1
            . (g `par` b1)
            . associatorInv @_ @s @a2 @b1
            . (s `par` swap' b1 a2)
            . associator @_ @s @b1 @a2
            . (f `par` a2)
            . associatorInv @_ @s @a1 @a2
        )
        \\ (a1 `par` a2)
        \\ (b1 `par` b2)
