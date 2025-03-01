{-# LANGUAGE TupleSections #-}

module Proarrow.Promonad.Writer where

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , first
  , obj2
  , second
  , swap'
  , unitObj
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid, Monoid (..), comultAct, counitAct, mappendAct, memptyAct)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Promonad (Procomonad (..))

data Writer w a b where
  Writer :: (Ob a, Ob b) => a ~> Act w b -> Writer w a b

instance (Ob (w :: m), MonoidalAction m k) => Profunctor (Writer w :: k +-> k) where
  dimap l r (Writer f) = Writer (act (obj @w) r . f . l) \\ r \\ l
  r \\ Writer f = r \\ f

instance (MonoidalAction m k) => Functor (Writer :: m -> k +-> k) where
  map f = f // Prof \(Writer @_ @b g) -> Writer (act f (obj @b) . g)

instance (Monoid (w :: m), MonoidalAction m k) => Promonad (Writer w :: k +-> k) where
  id = Writer (memptyAct @w)
  Writer @_ @c g . Writer f = Writer (mappendAct @w @c . act (obj @w) g . f)

instance (Comonoid (w :: m), MonoidalAction m k) => Procomonad (Writer w :: k +-> k) where
  extract (Writer f) = counitAct @w . f
  duplicate (Writer @_ @b f) = Writer (comultAct @w @b . f) :.: Writer id \\ f

instance (Ob (w :: m), MonoidalAction m k, SymMonoidal m) => Strong m (Writer w :: k +-> k) where
  act @a @b @x @y f (Writer g) =
    Writer (multiplicatorInv @m @k @w @b @y . act (swap @_ @b @w) (obj @y) . multiplicator @m @k @b @w @y . act f g)
      \\ act (obj @a) (obj @x)
      \\ act (obj @b) (obj @y)
      \\ f

instance (Monoid (w :: k), SelfAction k, SymMonoidal k) => MonoidalProfunctor (Writer w :: k +-> k) where
  par0 = id \\ unitObj @k
  Writer @x1 @x2 f `par` Writer @y1 @y2 g =
    Writer
      ( associator @k @w @x2 @y2
          . ((first @x2 (mappend @w) . associatorInv @k @w @w @x2 . swap' f (obj @w)) `par` obj @y2)
          . associatorInv @k @x1 @w @y2
          . second @x1 g
      )
      \\ obj2 @x1 @y1
      \\ obj2 @x2 @y2
