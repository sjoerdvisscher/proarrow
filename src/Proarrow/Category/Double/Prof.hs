-- {-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Double.Prof where

import Data.Function (($))

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Bicategory.Co (COK (..), Co (..))
import Proarrow.Category.Bicategory.Prof (PROFK, Prof (..), ProfCorepC, ProfK (..))
import Proarrow.Category.Double (Companion, Conjoint, Equipment (..), HasCompanions (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), UN, obj, (//))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Identity (Id (..))

instance HasCompanions PROFK (COK (ProfK ProfCorepC)) where
  type Companion PROFK (COK (ProfK ProfCorepC)) p = PK (UN PK (UN CO p))
  mapCompanion (Co (Prof n)) = Prof n
  compToId = Prof id
  compFromId = Prof id
  compToCompose (Co f) (Co g) = Prof id \\ f \\ g
  compFromCompose (Co f) (Co g) = Prof id \\ f \\ g

instance (Corepresentable p) => Adjunction (StarCorep p) p where
  unit :: forall a. (Ob a) => (p :.: StarCorep p) a a
  unit = let pa = corepMap @p (obj @a) in cotabulate pa :.: StarCorep pa
  counit (StarCorep f :.: p) = coindex p . f

instance Equipment PROFK (COK (ProfK ProfCorepC)) where
  type Conjoint PROFK (COK (ProfK ProfCorepC)) p = PK (StarCorep (UN PK (UN CO p)))
  mapConjoint (Co (Prof @p @q n)) = Prof \(StarCorep @b f) -> StarCorep (coindex (n (cotabulate @(UN PK p) @b (corepMap @(UN PK p) (obj @b)))) . f)
  conjToId = Prof (Id . unStarCorep)
  conjFromId = Prof \(Id f) -> StarCorep f \\ f
  conjToCompose (Co (Prof @f _)) (Co Prof{}) = Prof \(StarCorep @b h) -> StarCorep h :.: StarCorep id \\ corepMap @(UN PK f) (obj @b)
  conjFromCompose (Co Prof{}) (Co (Prof @g _)) = Prof \(StarCorep f :.: StarCorep g) -> StarCorep (corepMap @(UN PK g) g . f)

type StarCorep :: PRO a b -> PRO b a
data StarCorep p a b where
  StarCorep :: (Ob b) => {unStarCorep :: a ~> (p %% b)} -> StarCorep p a b
instance (Corepresentable p) => Profunctor (StarCorep p) where
  dimap f g (StarCorep p) = g // StarCorep $ dimap f (corepMap @p g) p
  r \\ StarCorep p = r \\ p
