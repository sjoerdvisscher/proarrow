-- | The constant functor as a 'Proarrow.Functor.FunctorForRep', sending every object to @c@. Its
-- representable profunctor @Rep (Constant c)@ is the viewing carrier used by 'Proarrow.Optic.Getter.view'.
module Proarrow.Profunctor.Instance.Constant where

import Proarrow.Core (CategoryOf (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..))

data family Constant :: k -> j +-> k
instance (CategoryOf j, CategoryOf k, Ob c) => FunctorForRep (Constant c :: j +-> k) where
  type Constant c @ a = c
  fmap _ = id
