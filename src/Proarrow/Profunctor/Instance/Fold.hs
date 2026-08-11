{-# LANGUAGE AllowAmbiguousTypes #-}

-- from Data.Fold.M of the Folds package
module Proarrow.Profunctor.Instance.Fold where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, leftUnitorInvWith, swapInner)
import Proarrow.Category.Monoidal.Action (CoprodAction, ProdAction)
import Proarrow.Category.Monoidal.Applicative (Applicative (..))
import Proarrow.Category.Monoidal.Closed (BiCCC)
import Proarrow.Category.Monoidal.Distributive (distLProd, distRProd)
import Proarrow.Category.Monoidal.Strength (Costrong (..), Strong (..))
import Proarrow.Colimit.BinaryCoproduct (COPROD (..), HasBinaryCoproducts (..), right)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Functor (map)
import Proarrow.Limit.BinaryProduct (Cartesian, HasBinaryProducts (..), PROD (..))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Promonad (Procomonad (..))

data Fold a b where
  Fold :: (Ob m) => (m ~> b) -> (a ~> m) -> (m ** m ~> m) -> (Unit ~> m) -> Fold a b

instance (CategoryOf k) => Profunctor (Fold :: k +-> k) where
  dimap f g (Fold k h m z) = Fold (g . k) (h . f) m z
  r \\ Fold f g _ _ = r \\ f \\ g

instance (CategoryOf k) => Procomonad (Fold :: k +-> k) where
  proextract (Fold f g _ _) = f . g
  produplicate (Fold f g m z) = Fold id g m z :.: Fold f id m z

instance (SymMonoidal k) => MonoidalProfunctor (Fold :: k +-> k) where
  one = Fold id id leftUnitor id
  Fold @m f g m z ** Fold @n f' g' m' z' =
    withOb2 @k @m @n P.$
      Fold (f ** f') (g ** g') ((m ** m') . swapInner @m @n @m @n) ((z ** z') . leftUnitorInv)

instance (BiCCC k) => Strong CoprodAction (Fold :: k +-> k) where
  act @(COPR a) (Fold @m k h m z) = withObCoprod @k @a @m P.$ Fold (obj @a +++ k) (right @a h) (step m) (rgt @_ @a @m . z)
    where
      step :: (Ob m, Ob a, Ob (a || m)) => (m && m) ~> m -> (a || m) && (a || m) ~> (a || m)
      step mult = (lft @k @a @m . fst @k @a @(a || m) ||| (snd @k @m @a +++ mult) . distLProd @m @a @m) . distRProd @a @m @(a || m)

instance (Cartesian k) => Costrong ProdAction (Fold :: k +-> k) where
  coact @(PR a) @_ @y (Fold f g m z) = Fold (snd @k @a @y . f) (g . leftUnitorInvWith (fst @k @a @y . f . z)) m z

trav :: (Applicative f) => Fold a b -> Fold (f a) (f b)
trav (Fold @m k h m z) = Fold (map k) (map h) (liftA2 @_ @m @m m) (pure z)

instance Corepresentable (Fold :: Type +-> Type) where
  type Fold %% a = [a]
  cotabulate f = Fold f (: []) mappend mempty
  coindex (Fold f g m z) xs = f (go xs)
    where
      go [] = z ()
      go (x : xs') = m (g x, go xs')
  corepMap = map
