{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Yoneda where

import Data.Function (($))

import Proarrow.Category.Instance.Prof (Prof (Prof))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (//), (:~>), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Cofree (HasCofree (..))
import Proarrow.Profunctor.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Star (Star, pattern Star)
import Proarrow.Category.Opposite (OPPOSITE(..), Op(..))
import Proarrow.Category.Instance.Nat (Nat(..))

type Yoneda :: (j +-> k) -> j +-> k
data Yoneda p a b where
  Yoneda :: (Ob a, Ob b) => {unYoneda :: Yo a (OP b) :~> p} -> Yoneda p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Yoneda (p :: j +-> k)) where
  dimap l r (Yoneda k) = l // r // Yoneda \(Yo ca bd) -> k $ Yo (l . ca) (bd . r)
  r \\ Yoneda{} = r

instance Functor Yoneda where
  map (Prof n) = Prof \(Yoneda k) -> Yoneda (n . k)

instance Promonad (Star Yoneda) where
  id = Star (Prof mkYoneda)
  Star (Prof l) . Star (Prof r) = Star (Prof (l . yoneda . r))

instance Promonad (Costar Yoneda) where
  id = Costar (Prof yoneda)
  Costar (Prof l) . Costar (Prof r) = Costar (Prof (l . mkYoneda . r))

instance HasCofree Profunctor where
  type Cofree Profunctor = Star Yoneda
  lower' (Star (Prof n)) = Prof (yoneda . n)
  section' (Prof n) = Star (Prof (mkYoneda . n))

yoneda :: (CategoryOf j, CategoryOf k) => Yoneda (p :: j +-> k) :~> p
yoneda (Yoneda k) = k $ Yo id id

mkYoneda :: (Profunctor p) => p :~> Yoneda p
mkYoneda p = p // Yoneda \(Yo ca bd) -> dimap ca bd p

-- | Yoneda embedding
type Yo :: k -> OPPOSITE j -> j +-> k
data Yo a b c d where
  Yo :: c ~> a -> b ~> d -> Yo a (OP b) c d

instance (CategoryOf j, CategoryOf k) => Profunctor (Yo (a :: k) (OP b :: OPPOSITE j) :: j +-> k) where
  dimap l r (Yo f g) = Yo (f . l) (r . g)
  r \\ Yo f g = r \\ f \\ g
instance (CategoryOf j, CategoryOf k) => Functor (Yo (a :: k) :: OPPOSITE j -> j +-> k) where
  map (Op f) = Prof \(Yo ca bd) -> Yo ca (bd . f)
instance (CategoryOf j, CategoryOf k) => Functor (Yo :: k -> OPPOSITE j -> j +-> k) where
  map f = Nat (Prof \(Yo ca bd) -> Yo (f . ca) bd)