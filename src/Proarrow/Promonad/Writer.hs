{-# LANGUAGE TupleSections #-}

module Proarrow.Promonad.Writer where

import Prelude (($))

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , first
  , second
  , swap'
  , unitObj
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..), actHom, strongPar0)
import Proarrow.Category.Monoidal.Distributive (Traversable (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, obj, tgt, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid, Monoid (..), comultAct, counitAct, mappendAct, memptyAct)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)
import Proarrow.Promonad (Procomonad (..))

data Writer w a b where
  Writer :: (Ob b) => a ~> Act w b -> Writer w a b

instance (Ob (w :: m), MonoidalAction m k) => Profunctor (Writer w :: k +-> k) where
  dimap = dimapRep
  r \\ Writer f = r \\ f

instance (Ob (w :: m), MonoidalAction m k) => Representable (Writer w :: k +-> k) where
  type Writer w % a = Act w a
  index (Writer f) = f
  tabulate f = Writer f
  repMap f = actHom (obj @w) f

instance (MonoidalAction m k) => Functor (Writer :: m -> k +-> k) where
  map f = f // Prof \(Writer @b g) -> Writer (actHom f (obj @b) . g)

instance (Monoid (w :: m), MonoidalAction m k) => Promonad (Writer w :: k +-> k) where
  id = Writer (memptyAct @w)
  Writer @c g . Writer f = Writer (mappendAct @w @c . actHom (obj @w) g . f)

instance (Comonoid (w :: m), MonoidalAction m k) => Procomonad (Writer w :: k +-> k) where
  extract (Writer f) = counitAct @w . f
  duplicate (Writer @b f) = Writer (comultAct @w @b . f) :.: Writer id \\ f

instance (Ob (w :: m), MonoidalAction m k, SymMonoidal m) => Strong m (Writer w :: k +-> k) where
  act @a @b @x @y f (Writer g) =
    Writer (multiplicatorInv @m @k @w @b @y . actHom (swap @_ @b @w) (obj @y) . multiplicator @m @k @b @w @y . actHom f g)
      \\ actHom (obj @a) (obj @x)
      \\ actHom (obj @b) (obj @y)
      \\ f
      \\ g

-- | Note: This is only premonoidal, not monoidal, unless the monoid is commutative.
instance (Monoid (w :: k), SelfAction k) => MonoidalProfunctor (Writer w :: k +-> k) where
  par0 = id \\ unitObj @k
  Writer @x2 @x1 f `par` Writer @y2 @y1 g =
    f //
      g //
        withOb2 @_ @x1 @y1 $
          withOb2 @_ @x2 @y2 $
            Writer
              ( associator @k @w @x2 @y2
                  . ((first @x2 (mappend @w) . associatorInv @k @w @w @x2 . swap' f (obj @w)) `par` obj @y2)
                  . associatorInv @k @x1 @w @y2
                  . second @x1 g
              )

instance (Monoid (w :: k), SelfAction k) => Traversable (Writer w :: k +-> k) where
  traverse (Writer f :.: p) = let wp = unId (strongPar0 @w) `act` p in lmap f wp :.: Writer (tgt wp) \\ wp \\ p