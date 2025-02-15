{-# LANGUAGE TupleSections #-}

module Proarrow.Promonad.Writer where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), leftUnitorInvWith, obj2)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Helper.CCC
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), associatorProd, associatorProdInv, diag, second)
import Proarrow.Object.Exponential (BiCCC)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Promonad (Procomonad (..))

data Writer m a b where
  Writer :: (Ob a, Ob b) => a ~> m && b -> Writer m a b

instance (BiCCC k, Ob m) => Profunctor (Writer m :: k +-> k) where
  dimap l r (Writer f) = Writer (second @m r . f . l) \\ r \\ l
  r \\ Writer f = r \\ f

instance (BiCCC k, Monoid m) => Promonad (Writer m :: k +-> k) where
  id = Writer (leftUnitorInvWith (mempty @m))
  Writer @_ @c g . Writer f = Writer (((mappend :: m && m ~> m) *** obj @c) . associatorProdInv @m @m @c . (obj @m *** g) . f)

instance (BiCCC k, Ob m) => Procomonad (Writer m :: k +-> k) where
  extract (Writer f) = snd @_ @m . f
  duplicate (Writer @_ @b f) = Writer (associatorProd @m @m @b . (diag @m *** obj @b) . f) :.: Writer id \\ (obj @m *** obj @b)

instance (BiCCC k, Monoid m) => MonoidalProfunctor (Writer m :: k +-> k) where
  par0 = id
  Writer @x1 @x2 f `par` Writer @y1 @y2 g =
    Writer
      ( (obj @m *** (obj2 @x2 @y2 :: x2 && y2 ~> x2 ** y2))
          . toCCC @(F x1 * F y1) @(F m * (F x2 * F y2))
            ( lam \(x1 :& y1) ->
                let f' = lift @(F x1) @(F m * F x2) f
                    g' = lift @(F y1) @(F m * F y2) g
                    mappend' = lift @(F m * F m) @(F m) mappend
                in case (f' x1, g' y1) of (m :& x2, m' :& y2) -> mappend' (m :& m') :& (x2 :& y2)
            )
      )
      \\ obj2 @x1 @y1
      \\ obj2 @x2 @y2
