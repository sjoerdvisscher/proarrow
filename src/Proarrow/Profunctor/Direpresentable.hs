module Proarrow.Profunctor.Direpresentable where

import Prelude (($))

import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..), withMappedOb)

type Direp :: (j +-> k) -> (i +-> k) -> i +-> j
data Direp f g a b where
  Direp :: (Ob a, Ob b) => (f @ a) ~> (g @ b) -> Direp f g a b

instance (FunctorForRep f, FunctorForRep g) => Profunctor (Direp f g) where
  dimap l r (Direp f) = Direp (fmap @g r . f . fmap @f l) \\ r \\ l
  r \\ Direp{} = r

instance (Thin k, FunctorForRep f, FunctorForRep g) => ThinProfunctor (Direp (f :: j +-> k) (g :: i +-> k)) where
  type HasArrow (Direp (f :: j +-> k) g) a b = HasArrow (Hom k) (f @ a) (g @ b)
  arr @a @b = withMappedOb @f @a $ withMappedOb @g @b $ Direp (arr @(Hom k) @(f @ a) @(g @ b))
  withArr (Direp f) r = withArr f r
