module Proarrow.Category.Bicategory.Mod where

import Proarrow.Category.Bicategory (Bicategory (..), Monad (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, Obj, dimapDefault)

type data MONK kk where
  MON :: kk a a -> MONK kk
type instance UN MON (MON s) = s
type family MONObj0 (s :: MONK (kk :: CAT k)) :: k
type instance MONObj0 (MON (s :: kk a a)) = a

type data MODK kk (s :: MONK kk) (t :: MONK kk) = MOD (kk (MONObj0 t) (MONObj0 s))
type family UNMOD (p :: MODK kk s t) :: kk (MONObj0 t) (MONObj0 s)
type instance UNMOD (MOD p) = p

type IsMON kk s = Is (MON @kk @(MONObj0 s)) s

type Mod :: forall {kk} {s} {t}. CAT (MODK kk s t)
data Mod p q where
  Mod
    :: (s :: kk i i) `O` (p :: kk j i) `O` (t :: kk j j) ~> p -> p ~> q -> s `O` q `O` t ~> q -> Mod (MOD p :: MODK kk (MON s) (MON t)) (MOD q)
instance (Bicategory kk, Ob0 kk (MONObj0 s), Ob0 kk (MONObj0 t), IsMON kk s, IsMON kk t) => Profunctor (Mod :: CAT (MODK kk s t)) where
  dimap = dimapDefault
  r \\ Mod _ f _ = r \\ f
instance (Bicategory kk, Ob0 kk (MONObj0 s), Ob0 kk (MONObj0 t), IsMON kk s, IsMON kk t) => Promonad (Mod :: CAT (MODK kk s t)) where
  id :: forall (a :: MODK kk s t). (Ob a) => Mod a a
  id = Mod @kk @(UN MON s) @(UNMOD a) @(UN MON t) @(UNMOD a) _ id _
  Mod _ f q . Mod p g _ = Mod p (f . g) q
instance (Bicategory kk, Ob0 kk (MONObj0 s), Ob0 kk (MONObj0 t), IsMON kk s, IsMON kk t) => CategoryOf (MODK kk s t) where
  type (~>) = Mod
  type Ob (p :: MODK kk s t) = (p ~ MOD (UNMOD p), Ob (UNMOD p))

instance (Bicategory kk) => Bicategory (MODK kk) where
  type Ob0 (MODK kk) (s :: MONK kk) = (Monad (UN MON s :: kk (MONObj0 s) (MONObj0 s)), Ob0 kk (MONObj0 s), IsMON kk s)
  type I @(MODK kk) @(i :: MONK kk) = MOD (UN MON i)
  type MOD p `O` MOD q = MOD (q `O` p)
  Mod p f q `o` Mod p' g q' = let fg = f `o` g in Mod _ fg _
  -- leftUnitor (Mod p) = let lp = leftUnitor p in Mod lp \\ lp
