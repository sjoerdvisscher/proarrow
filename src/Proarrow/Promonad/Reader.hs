module Proarrow.Promonad.Reader where

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), leftUnitorInvWith, obj2)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Helper.CCC
  ( FK (F)
  , lam
  , lift
  , toCCC
  , pattern (:&)
  , type (*)
  )
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), associatorProdInv)
import Proarrow.Object.Exponential (BiCCC)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Promonad.Writer (Writer (..))

data Reader r a b where
  Reader :: (Ob a, Ob b) => (r && a) ~> b -> Reader r a b

instance (BiCCC k, Ob r) => Profunctor (Reader r :: k +-> k) where
  dimap l r (Reader f) = Reader (r . f . (obj @r *** l)) \\ r \\ l
  r \\ Reader f = r \\ f

instance (BiCCC k, Ob r) => Promonad (Reader r :: k +-> k) where
  id = Reader (snd @k @r)
  Reader @b @c g . Reader @a f = Reader (toCCC @(F r * F a) @(F c) (lam \(r :& a) -> lift @(F r * F b) g (r :& lift f (r :& a))))

instance (Monoid m, BiCCC k) => Procomonad (Reader m :: k +-> k) where
  extract (Reader f) = f . leftUnitorInvWith (mempty @m)
  duplicate (Reader @a f) = Reader id :.: Reader (f . ((mappend :: m && m ~> m) *** obj @a) . associatorProdInv @m @m @a) \\ f

instance (BiCCC k, Ob r) => MonoidalProfunctor (Reader r :: k +-> k) where
  par0 = id
  Reader @x1 @x2 f `par` Reader @y1 @y2 g =
    Reader
      ( ( toCCC @(F r * (F x1 * F y1)) @(F x2 * F y2)
            ( lam \(r :& (x :& y)) ->
                let f' = lift @(F r * F x1) f
                    g' = lift @(F r * F y1) g
                in f' (r :& x) :& g' (r :& y)
            )
        )
          . (obj @r *** (obj2 @x1 @y1 :: x1 ** y1 ~> x1 && y1))
      )
      \\ obj2 @x1 @y1
      \\ obj2 @x2 @y2

instance (BiCCC k, Ob r) => Adjunction (Writer r :: k +-> k) (Reader r) where
  unit @a = Reader id :.: Writer id \\ (obj @r *** obj @a)
  counit (Writer f :.: Reader g) = g . f