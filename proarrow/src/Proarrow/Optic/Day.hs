{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A third way to combine two flavors, alongside 'Proarrow.Optic.Prod.ProdRes' and
-- 'Proarrow.Optic.Sum.SumRes': via the Day convolution, which -- unlike those two -- keeps both
-- witnesses in the *same* ambient categories @j@\/@k@ (it needs 'Monoidal' structure there to
-- split objects across the two witnesses, rather than pairing\/summing two independent
-- categories).
module Proarrow.Optic.Day where

import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), type (**))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (CompactFlavor, ExOptic (..), FLAVOR, Optic, Prostrong (..), ex2prof, withLegs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Day (Day, day)
import Proarrow.Profunctor.Instance.Identity (Id (..))

type DayRes :: FLAVOR j k -> FLAVOR j k -> FLAVOR j k
class DayRes w1 w2 (p :: k +-> k) (q :: j +-> j)
instance (w1 p1 q1, w2 p2 q2) => DayRes w1 w2 (Day p1 p2) (Day q1 q2)
instance (CategoryOf k, CategoryOf j) => DayRes w1 w2 (Id :: CAT k) (Id :: CAT j)
instance (DayRes w1 w2 f f', DayRes w1 w2 g g') => DayRes w1 w2 (f :.: g) (g' :.: f')

dayOptic
  :: forall {j} {k} (w1 :: FLAVOR j k) (w2 :: FLAVOR j k) s1 t1 a1 b1 s2 t2 a2 b2
   . (Monoidal j, Monoidal k, CompactFlavor w1, CompactFlavor w2)
  => Optic (Prostrong w1) s1 t1 a1 b1
  -> Optic (Prostrong w2) s2 t2 a2 b2
  -> Optic (Prostrong (DayRes w1 w2)) (s1 ** s2) (t1 ** t2) (a1 ** a2) (b1 ** b2)
dayOptic o1 o2 =
  withLegs
    ( \l1@Objs r1@Objs ->
        withLegs
          ( \l2@Objs r2@Objs ->
              withOb2 @k @a1 @a2 $
                withOb2 @j @b1 @b2 $
                  ex2prof (ExProstrong (day l1 l2 :.: ExIso id id :.: day r1 r2)) \\ l1 \\ r1 \\ l2 \\ r2
          )
          o2
    )
    o1
