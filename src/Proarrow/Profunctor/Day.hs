{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Day where

import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), swap, swapInner)
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), lmap, obj, rmap, src, tgt, (//))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Identity (Id (..))

data DayUnit a b where
  DayUnit :: a ~> Unit -> Unit ~> b -> DayUnit a b

instance (CategoryOf j, CategoryOf k) => Profunctor (DayUnit :: PRO j k) where
  dimap l r (DayUnit f g) = DayUnit (f . l) (r . g)
  r \\ DayUnit f g = r \\ f \\ g

data Day p q a b where
  Day :: forall p q a b c d e f. a ~> c ** e -> p c d -> q e f -> d ** f ~> b -> Day p q a b

instance (Profunctor p, Profunctor q) => Profunctor (Day p q) where
  dimap l r (Day f p q g) = Day (lmap l f) p q (rmap r g)
  r \\ Day f _ _ g = r \\ f \\ g

instance (Profunctor p) => Functor (Day p) where
  map (Prof n) = Prof \(Day f p q g) -> Day f p (n q) g

instance Functor Day where
  map (Prof n) = Nat (Prof \(Day f p q g) -> Day f (n p) q g)

instance (Monoidal j, Monoidal k) => Monoidal (PRO j k) where
  type Unit = DayUnit
  type p ** q = Day p q
  Prof m `par` Prof n = Prof \(Day f p q g) -> Day f (m p) (n q) g
  leftUnitor (Prof n) = Prof \(Day f (DayUnit h i) q g) -> n (dimap (leftUnitor (src q) . (h `par` src q) . f) (g . (i `par` tgt q) . leftUnitorInv (tgt q)) q)
  leftUnitorInv (Prof n) = Prof \q -> Day (leftUnitorInv (src q)) (DayUnit id id) (n q) (leftUnitor (tgt q))
  rightUnitor (Prof n) = Prof \(Day f p (DayUnit h i) g) -> n (dimap (rightUnitor (src p) . (src p `par` h) . f) (g . (tgt p `par` i) . rightUnitorInv (tgt p)) p)
  rightUnitorInv (Prof n) = Prof \p -> Day (rightUnitorInv (src p)) (n p) (DayUnit id id) (rightUnitor (tgt p))
  associator Prof{} Prof{} Prof{} = Prof \(Day f1 (Day f2 p2 q2 g2) q1 g1) ->
    let f = associator (src p2) (src q2) (src q1) . (f2 `par` src q1) . f1
        g = g1 . (g2 `par` tgt q1) . associatorInv (tgt p2) (tgt q2) (tgt q1)
    in Day f p2 (Day (src q2 `par` src q1) q2 q1 (tgt q2 `par` tgt q1)) g
  associatorInv Prof{} Prof{} Prof{} = Prof \(Day f1 p1 (Day f2 p2 q2 g2) g1) ->
    let f = associatorInv (src p1) (src p2) (src q2) . (src p1 `par` f2) . f1
        g = g1 . (tgt p1 `par` g2) . associator (tgt p1) (tgt p2) (tgt q2)
    in Day f (Day (src p1 `par` src p2) p1 p2 (tgt p1 `par` tgt p2)) q2 g

instance (SymMonoidal j, SymMonoidal k) => SymMonoidal (PRO j k) where
  swap' Prof{} Prof{} = Prof \(Day @_ @_ @_ @_ @c @d @e @f f p q g) -> Day (swap @c @e . f) q p (g . swap @f @d) \\ p \\ q

duoidal
  :: (Monoidal k, Profunctor (p :: PRO i k), Profunctor p', Profunctor q, Profunctor q')
  => (p :.: p') `Day` (q :.: q') ~> (p `Day` q) :.: (p' `Day` q')
duoidal = Prof \(Day f (p :.: p') (q :.: q') g) -> let b = tgt p `par` tgt q in Day f p q b :.: Day b p' q' g

instance (Monoidal k) => Monoid (Id :: PRO k k) where
  mempty = Prof \(DayUnit f g) -> Id (g . f)
  mappend = Prof \(Day f (Id p) (Id q) g) -> Id (g . (p `par` q) . f)

-- instance Monoidal k => Comonoid (E (PK (DayUnit :: PRO k k))) where
--   counit = Endo (Bi.Prof \(DayUnit f g) -> g . f)
--   comult = Endo (Bi.Prof \(DayUnit f g) -> DayUnit f id :.: DayUnit id g)

data DayExp p q a b where
  DayExp :: forall p q a b. (Ob a, Ob b) => (forall c d e f. e ~> a ** c -> b ** d ~> f -> p c d -> q e f) -> DayExp p q a b

instance (Monoidal j, Monoidal k, Profunctor p, Profunctor q) => Profunctor (DayExp (p :: PRO j k) q) where
  dimap l r (DayExp n) = l // r // DayExp \f g p -> n ((l `par` src p) . f) (g . (r `par` tgt p)) p
  r \\ DayExp n = r \\ n

instance (Monoidal j, Monoidal k) => Closed (PRO j k) where
  type p ~~> q = DayExp p q
  curry' Prof{} Prof{} (Prof n) = Prof \p -> p // DayExp \f g q -> n (Day f p q g)
  uncurry' Prof{} Prof{} (Prof n) = Prof \(Day f p q g) -> case n p of DayExp h -> h f g q
  (^^^) (Prof n) (Prof m) = Prof \(DayExp k) -> DayExp \f g p -> n (k f g (m p))

multDayExp
  :: (SymMonoidal j, SymMonoidal k, Profunctor (p :: PRO j k), Profunctor q, Profunctor p', Profunctor q')
  => (p ~~> q) `Day` (p' ~~> q') ~> (p `Day` p') ~~> (q `Day` q')
multDayExp = Prof \(Day @_ @_ @_ @_ @c @d @e @f g (DayExp pq) (DayExp pq') h) ->
  g
    // h
    // DayExp
      ( \l r (Day i p p' j) ->
          p
            // p'
            // let c = obj @c; d = obj @d; e = obj @e; f = obj @f; c' = src p; d' = tgt p; e' = src p'; f' = tgt p'
               in Day
                    (swapInner c e c' e' . (g `par` i) . l)
                    (pq (c `par` c') (d `par` d') p)
                    (pq' (e `par` e') (f `par` f') p')
                    (r . (h `par` j) . swapInner d d' f f')
      )

newtype MonoidInProf p a b = MonoidInProf (p a b)
instance (Profunctor p) => Profunctor (MonoidInProf p) where
  dimap l r (MonoidInProf p) = MonoidInProf (dimap l r p)
  r \\ MonoidInProf p = r \\ p

instance (Profunctor p, MonoidalProfunctor p) => Monoid (MonoidInProf p) where
  mempty = Prof \(DayUnit f g) -> MonoidInProf (dimap f g lift0)
  mappend = Prof \(Day f (MonoidInProf p) (MonoidInProf q) g) -> MonoidInProf (dimap f g (lift2 p q))
