{-# LANGUAGE AllowAmbiguousTypes #-}

-- from Data.Fold.M of the Folds package
module Proarrow.Profunctor.Fold where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, swapInner)
import Proarrow.Category.Monoidal.Action (Strong (..), Costrong (..), MonoidalAction (..), actHom)
import Proarrow.Category.Monoidal.Applicative (Applicative (..))
import Proarrow.Category.Monoidal.Distributive (distLProd, distRProd)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (//), type (+->), obj)
import Proarrow.Functor (map)
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.BinaryCoproduct (COPROD (..), Coprod (..), CoprodAction, HasBinaryCoproducts (..), right)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), ProdAction)
import Proarrow.Object.Exponential (BiCCC)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Promonad (Procomonad (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id(..))



data Fold a b where
  Fold :: (Ob m) => (m ~> b) -> (a ~> m) -> (m ** m ~> m) -> (Unit ~> m) -> Fold a b

instance (CategoryOf k) => Profunctor (Fold :: k +-> k) where
  dimap f g (Fold k h m z) = Fold (g . k) (h . f) m z
  r \\ Fold f g _ _ = r \\ f \\ g

instance CategoryOf k => Procomonad (Fold :: k +-> k) where
  extract (Fold f g _ _) = f . g
  duplicate (Fold f g m z) = Fold id g m z :.: Fold f id m z

instance (SymMonoidal k) => MonoidalProfunctor (Fold :: k +-> k) where
  par0 = Fold id id leftUnitor id
  Fold @m f g m z `par` Fold @n f' g' m' z' =
    withOb2 @k @m @n P.$
      Fold (f `par` f') (g `par` g') ((m `par` m') . swapInner @m @n @m @n) ((z `par` z') . leftUnitorInv)

instance (CoprodAction k, BiCCC k) => Strong (COPROD k) (Fold :: k +-> k) where
  act (Coprod @_ @a (Id f)) (Fold @m k h m z) = f // withObCoprod @k @a @m P.$ Fold (f +++ k) (right @a h) (step m) (rgt @_ @a @m . z)
    where
      step :: (Ob m, Ob a, Ob (a || m)) => (m && m) ~> m -> (a || m) && (a || m) ~> (a || m)
      step mult = (lft @k @a @m . fst @k @a @(a || m) ||| (snd @k @m @a +++ mult) . distLProd @m @a @m) . distRProd @a @m @(a || m)

instance (ProdAction k) => Costrong k (Fold :: k +-> k) where
  coact @a @x @y (Fold f g m z) = Fold (snd @k @a @y . f) (g . actHom (fst @k @a @y . f . z) (obj @x) . unitorInv @k @k @x) m z

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
