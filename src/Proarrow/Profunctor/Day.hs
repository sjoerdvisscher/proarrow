{-# LANGUAGE UndecidableInstances #-}
module Proarrow.Profunctor.Day where

import Data.Function (($))

import Proarrow.Core (BI, PRO, Profunctor(..), Category(..), type (~>), CategoryOf)
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (Tensor(..))
import Proarrow.Profunctor.Star (Star)
import Proarrow.Profunctor.Representable (Representable(..))
import Proarrow.Object (src, tgt)


type Day :: PRO j (j, j) -> PRO k (k, k) -> BI (PRO j k)
data Day s t pq a b where
  Day :: p a b -> q c d -> e ~> s % '(a, c) -> t % '(b, d) ~> f -> Day s t '(p, q) e f

instance (Profunctor p, Profunctor q) => Profunctor (Day s t '(p, q)) where
  dimap l r (Day p q f g) = Day p q (f . l) (r . g)
  r \\ Day _ _ f g = r \\ f \\ g

instance Functor (Day s t) where
  map (Prof l :**: Prof r) = Prof (\(Day p q f g) -> Day (l p) (r q) f g)


type DayUnit :: PRO j (j, j) -> PRO k (k, k) -> PRO j k
data DayUnit s t a b where
  DayUnit :: a ~> U s -> U t ~> b -> DayUnit s t a b

instance (CategoryOf j, CategoryOf k) => Profunctor (DayUnit (s :: PRO j (j, j)) (t :: PRO k (k, k))) where
  dimap l r (DayUnit f g) = DayUnit (f . l) (r . g)
  r \\ DayUnit f g = r \\ f \\ g

instance (Tensor s, Tensor t) => Tensor (Star (Day s t)) where
  type U (Star (Day s t)) = DayUnit s t
  leftUnitor = Prof $ \(Day (DayUnit l r) q f g) ->
    dimap
      (leftUnitor @s . repMap @s (l :**: src q) . f)
      (g . repMap @t (r :**: tgt q) . leftUnitorInv @t)
      q
    \\ q
  leftUnitorInv = Prof $ \q -> Day (DayUnit id id) q (leftUnitorInv @s) (leftUnitor @t) \\ q
  rightUnitor = Prof $ \(Day p (DayUnit l r) f g) ->
    dimap
      (rightUnitor @s . repMap @s (src p :**: l) . f)
      (g . repMap @t (tgt p :**: r) . rightUnitorInv @t)
      p
    \\ p
  rightUnitorInv = Prof $ \p -> Day p (DayUnit id id) (rightUnitorInv @s) (rightUnitor @t) \\ p
  associator' Prof{} Prof{} Prof{} = Prof $ \(Day (Day p q f g) r h i) ->
    Day p (Day q r (repMap @s $ src q :**: src r) (repMap @t $ tgt q :**: tgt r))
      (associator' @s (src p) (src q) (src r) . repMap @s (f :**: src r) . h)
      (i . repMap @t (g :**: tgt r) . associatorInv' @t (tgt p) (tgt q) (tgt r))
  associatorInv' Prof{} Prof{} Prof{} = Prof $ \(Day p (Day q r f g) h i) ->
    Day (Day p q (repMap @s $ src p :**: src q) (repMap @t $ tgt p :**: tgt q)) r
      (associatorInv' @s (src p) (src q) (src r) . repMap @s (src p :**: f) . h)
      (i . repMap @t (tgt p :**: g) . associator' @t (tgt p) (tgt q) (tgt r))