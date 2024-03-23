module Proarrow.Profunctor.Yoneda where

import Data.Kind (Type)
import Data.Function (($))

import Proarrow.Core (PRO, CategoryOf(..), Promonad(..), Profunctor(..), (//), (:~>))


type Yoneda :: (j -> k -> Type) -> PRO j k
data Yoneda p a b where
  Yoneda :: (Ob a, Ob b) => { getYoneda :: Yo a b :~> p } -> Yoneda p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Yoneda (p :: PRO j k)) where
  dimap l r (Yoneda k) = l // r // Yoneda \(Yo ca bd) -> k $ Yo (l . ca) (bd . r)
  r \\ Yoneda{} = r

yoneda :: (CategoryOf j, CategoryOf k) => Yoneda (p :: PRO j k) :~> p
yoneda (Yoneda k) = k $ Yo id id


-- | Yoneda embedding
data Yo a b c d = Yo (c ~> a) (b ~> d)
instance (CategoryOf j, CategoryOf k) => Profunctor (Yo (a :: j) (b :: k) :: PRO j k) where
  dimap l r (Yo f g) = Yo (f . l) (r . g)
  r \\ Yo f g = r \\ f \\ g
