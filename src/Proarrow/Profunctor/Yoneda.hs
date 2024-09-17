{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Yoneda where

import Data.Function (($))
import Data.Kind (Type)

import Proarrow.Category.Instance.Prof (Prof (Prof))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), (//), (:~>))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Cofree (HasCofree (..))
import Proarrow.Profunctor.Star (Star (..))

type Yoneda :: (j -> k -> Type) -> PRO j k
data Yoneda p a b where
  Yoneda :: (Ob a, Ob b) => {unYoneda :: Yo a b :~> p} -> Yoneda p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Yoneda (p :: PRO j k)) where
  dimap l r (Yoneda k) = l // r // Yoneda \(Yo ca bd) -> k $ Yo (l . ca) (bd . r)
  r \\ Yoneda{} = r

instance Functor Yoneda where
  map (Prof n) = Prof \(Yoneda k) -> Yoneda (n . k)

instance HasCofree Profunctor where
  type Cofree Profunctor = Star Yoneda
  lower' (Star (Prof n)) = Prof (yoneda . n)
  section' (Prof n) = Star (Prof (mkYoneda . n))

yoneda :: (CategoryOf j, CategoryOf k) => Yoneda (p :: PRO j k) :~> p
yoneda (Yoneda k) = k $ Yo id id

mkYoneda :: (Profunctor p) => p :~> Yoneda p
mkYoneda p = p // Yoneda \(Yo ca bd) -> dimap ca bd p

-- | Yoneda embedding
data Yo a b c d = Yo (c ~> a) (b ~> d)

instance (CategoryOf j, CategoryOf k) => Profunctor (Yo (a :: j) (b :: k) :: PRO j k) where
  dimap l r (Yo f g) = Yo (f . l) (r . g)
  r \\ Yo f g = r \\ f \\ g
