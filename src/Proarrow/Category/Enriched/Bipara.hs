module Proarrow.Category.Enriched.Bipara where

import Data.Kind (Type)
import Prelude (($), type (~))

import Proarrow.Category.Bicategory (Bicategory (I))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Category.Enriched (Arr, ECategory (..), V, type (%~>))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , associator'
  , associatorInv'
  , first
  , leftUnitorInv'
  , par
  , rightUnitor'
  , second
  )
import Proarrow.Core (CategoryOf (..), Is, Kind, PRO, Profunctor (..), Promonad (..), UN, obj, (//))
import Proarrow.Profunctor.Day (Day (..), DayUnit (..))

type BIPARAK :: Kind -> () -> Kind
data BIPARAK k ext where
  BIPARA :: k -> BIPARAK k i
type instance UN BIPARA (BIPARA a) = a

type instance V (BIPARAK k) = MonK (PRO k k)
type instance Arr (MonK (PRO k k)) (BIPARA a) (BIPARA b) = MK (Bipara a b)

type Bipara :: k -> k -> k -> k -> Type
data Bipara a b p q where
  Bipara :: (Ob p, Ob q) => b ** p ~> q ** a -> Bipara a b p q

instance (Monoidal k, Ob a, Ob b) => Profunctor (Bipara (a :: k) b) where
  dimap f g (Bipara h) = Bipara (first @a g . h . second @b f) \\ f \\ g
  r \\ Bipara{} = r

-- | Bipara as a profunctor enriched category.
instance (Monoidal k) => ECategory (BIPARAK k) where
  type EOb a = (Is BIPARA a, Ob (UN BIPARA a))

  eid :: forall {exta} (a :: k) (a' :: BIPARAK k exta). (a' ~ BIPARA a, EOb a') => I ~> (a' %~> a')
  eid = Mon2 $ Prof $ \(DayUnit f g) ->
    f // g // Bipara $
      let a = obj @a
      in (g `par` a) . leftUnitorInv' a . rightUnitor' a . (a `par` f)

  ecomp = Mon2 $ Prof $ \(Day g (Bipara @c @d @aa p) (Bipara @e @f @bb @cc q) h) ->
    g // h // Bipara $
      let c = obj @c; d = obj @d; e = obj @e; f = obj @f; aa = obj @aa; bb = obj @bb; cc = obj @cc
      in (h `par` cc)
          . associatorInv' d f cc
          . (d `par` q)
          . associator' d bb e
          . (p `par` e)
          . associatorInv' aa c e
          . (aa `par` g)
