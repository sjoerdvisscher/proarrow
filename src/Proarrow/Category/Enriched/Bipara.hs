module Proarrow.Category.Enriched.Bipara where

import Data.Kind (Type)
import Prelude (($))

import Proarrow.Category.Bicategory (Bicategory (I))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Category.Enriched (Arr, ECategory (..), V, type (%~>))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal, first, second, swap')
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
  Bipara :: (Ob p, Ob q) => a ** p ~> q ** b -> Bipara a b p q

instance (Monoidal k, Ob a, Ob b) => Profunctor (Bipara (a :: k) b) where
  dimap f g (Bipara h) = Bipara (first @b g . h . second @a f) \\ f \\ g
  r \\ Bipara{} = r

-- | Bipara as a profunctor enriched category.
instance (SymMonoidal k) => ECategory (BIPARAK k) where
  type EOb a = (Is BIPARA a, Ob (UN BIPARA a))

  eid :: forall {exta} (a :: BIPARAK k exta). (EOb a) => I ~> (a %~> a)
  eid = Mon2 $ Prof $ \(DayUnit f g) ->
    f // g // Bipara $
      let a = obj @(UN BIPARA a)
      in (g `par` a) . leftUnitorInv a . rightUnitor a . (a `par` f)

  ecomp = Mon2 $ Prof $ \(Day g (Bipara @c @d @bb @cc p) (Bipara @e @f @aa q) h) ->
    g // h // Bipara $
      let c = obj @c; d = obj @d; e = obj @e; f = obj @f; aa = obj @aa; bb = obj @bb; cc = obj @cc
      in ((h . swap' f d) `par` cc)
          . associatorInv f d cc
          . (f `par` p)
          . associator f bb c
          . (q `par` c)
          . associatorInv aa e c
          . (aa `par` (swap' c e . g))
