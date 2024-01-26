{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Profunctor.Day where

import Proarrow.Core (PRO, Profunctor(..), CategoryOf(..), Promonad(..), lmap, rmap)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Object (src, tgt)


data DayUnit a b where
  DayUnit :: a ~> Unit -> Unit ~> b -> DayUnit a b

instance (CategoryOf j, CategoryOf k) => Profunctor (DayUnit :: PRO j k) where
  dimap l r (DayUnit f g) = DayUnit (f . l) (r . g)
  r \\ DayUnit f g = r \\ f \\ g

data Day p q a b where
  Day :: a ~> c ** e -> p c d -> q e f -> d ** f ~> b -> Day p q a b

instance (Profunctor p, Profunctor q) => Profunctor (Day p q) where
  dimap l r (Day f p q g) = Day (lmap l f) p q (rmap r g)
  r \\ Day f _ _ g = r \\ f \\ g

instance (Monoidal j, Monoidal k) => Monoidal (PRO j k) where
  type Unit = DayUnit
  type p ** q = Day p q
  Prof m `par` Prof n = Prof \(Day f p q g) -> Day f (m p) (n q) g
  leftUnitor Prof{} = Prof \(Day f (DayUnit h i) q g) -> dimap (leftUnitor (src q) . (h `par` src q) . f) (g . (i `par` tgt q) . leftUnitorInv (tgt q)) q
  leftUnitorInv Prof{} = Prof \q -> Day (leftUnitorInv (src q)) (DayUnit id id) q (leftUnitor (tgt q))
  rightUnitor Prof{} = Prof \(Day f p (DayUnit h i) g) -> dimap (rightUnitor (src p) . (src p `par` h) . f) (g . (tgt p `par` i) . rightUnitorInv (tgt p)) p
  rightUnitorInv Prof{} = Prof \p -> Day (rightUnitorInv (src p)) p (DayUnit id id) (rightUnitor (tgt p))
  associator Prof{} Prof{} Prof{} = Prof \(Day f1 (Day f2 p2 q2 g2) q1 g1) ->
    let f = associator (src p2) (src q2) (src q1) . (f2 `par` src q1) . f1
        g = g1 . (g2 `par` tgt q1) . associatorInv (tgt p2) (tgt q2) (tgt q1)
    in Day f p2 (Day (src q2 `par` src q1) q2 q1 (tgt q2 `par` tgt q1)) g
  associatorInv Prof{} Prof{} Prof{} = Prof \(Day f1 p1 (Day f2 p2 q2 g2) g1) ->
    let f = associatorInv (src p1) (src p2) (src q2) . (src p1 `par` f2) . f1
        g = g1 . (tgt p1 `par` g2) . associator (tgt p1) (tgt p2) (tgt q2)
    in Day f (Day (src p1 `par` src p2) p1 p2 (tgt p1 `par` tgt p2)) q2 g