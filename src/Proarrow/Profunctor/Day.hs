module Proarrow.Profunctor.Day where

import Data.Function (($))

import Proarrow.Core (PRO, Profunctor(..), CategoryOf(..), Promonad(..), (//), (:~>))
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Monoidal (MONOIDAL, Monoidal (..))
import Proarrow.Category.Instance.List (List (..), type (++), obAppend)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Object (Obj, obj)

type PList :: [PRO j k] -> PRO [j] [k]
data PList ps as bs where
  PNil :: PList '[] '[] '[]
  PCons :: Ob p => p a b -> PList ps as bs -> PList (p ': ps) (a ': as) (b ': bs)

instance (CategoryOf j, CategoryOf k) => Profunctor (PList (ps :: [PRO j k])) where
  dimap Nil Nil PNil = PNil
  dimap (Cons l ls) (Cons r rs) (PCons p ps) = PCons (dimap l r p) (dimap ls rs ps)
  dimap Nil Cons{} p = case p of
  dimap Cons{} Nil p = case p of
  r \\ PNil = r
  r \\ PCons p ps = r \\ p \\ ps

instance (CategoryOf j, CategoryOf k) => Functor (PList :: [PRO j k] -> PRO [j] [k]) where
  map Nil = Prof \PNil -> PNil
  map (Cons (Prof n) ns) = ns // Prof \(PCons p ps) -> PCons (n p) (getProf (map ns) ps)

splitP
  :: forall ps1 ps2 as bs r. Ob ps1
  => PList (ps1 ++ ps2) as bs
  -> (forall as1 as2 bs1 bs2. (as ~ as1 ++ as2, bs ~ bs1 ++ bs2) => PList ps1 as1 bs1 -> PList ps2 as2 bs2 -> r)
  -> r
splitP = h (obj @ps1)
  where
    h :: forall qs as' bs'. Obj qs -> PList (qs ++ ps2) as' bs'
      -> (forall as1 as2 bs1 bs2. (as' ~ as1 ++ as2, bs' ~ bs1 ++ bs2) => PList qs as1 bs1 -> PList ps2 as2 bs2 -> r) -> r
    h Nil ps k = k PNil ps
    h (Cons _ qs) (PCons p ps) k = h qs ps (k . PCons p)

appendP :: PList ps1 as1 bs1 -> PList ps2 as2 bs2 -> PList (ps1 ++ ps2) (as1 ++ as2) (bs1 ++ bs2)
appendP PNil ps2 = ps2
appendP (PCons p ps1) ps2 = PCons p (appendP ps1 ps2)



type Day :: MONOIDAL j -> MONOIDAL k -> MONOIDAL (PRO j k)
data Day s t ps qs where
  Day :: (Ob ps, Ob qs) => { getDay :: PList ps :~> (s :.: PList qs :.: t) } -> Day s t ps qs

instance (CategoryOf j, CategoryOf k) => Profunctor (Day s t :: MONOIDAL (PRO j k)) where
  dimap l r (Day f) = l // r // Day \ps -> case f (getProf (map l) ps) of
    s :.: qs :.: t -> s :.: getProf (map r) qs :.: t
  r \\ Day{} = r

instance (CategoryOf j, CategoryOf k, Promonad s, Promonad t) => Promonad (Day s t :: MONOIDAL (PRO j k)) where
  id = Day \ps -> id :.: ps :.: id \\ ps
  Day f . Day g = Day \ps -> case g ps of
    s1 :.: qs :.: t1 -> case f qs of
      s2 :.: rs :.: t2 -> (s2 . s1) :.: rs :.: (t1 . t2)

instance (CategoryOf j, CategoryOf k, Monoidal s, Monoidal t) => Monoidal (Day s t :: MONOIDAL (PRO j k)) where
  par (Day @ps1 @qs1 f) (Day @ps2 @qs2 g) = obAppend @ps1 @ps2 $ obAppend @qs1 @qs2 $
    Day \ps -> splitP @ps1 @ps2 ps \ps1 ps2 -> case (f ps1, g ps2) of
      (s1 :.: qs1 :.: t1, s2 :.: qs2 :.: t2) -> par s1 s2 :.: appendP qs1 qs2 :.: par t1 t2


