module Proarrow.Category.Bicategory.Mod where

import Proarrow.Category.Bicategory (Bicategory (..), Bimodule (..), Monad (..), Path (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, Obj, dimapDefault)

type data MONK kk where
  MON :: kk a a -> MONK kk
type instance UN MON (MON s) = s
type family MONObj0 (s :: MONK (kk :: CAT k)) :: k where
  MONObj0 (MON (s :: kk a a)) = a

type data MODK kk (s :: MONK kk) (t :: MONK kk) = MOD (Path kk (MONObj0 s) (MONObj0 t))
type family UNMOD (p :: MODK kk s t) :: Path kk (MONObj0 s) (MONObj0 t) where
  UNMOD (MOD p) = p

type Mod :: forall {kk} {s} {t}. CAT (MODK kk s t)
data Mod p q where
  Mod
    :: (s' ~ UN MON s ::: Nil, t' ~ UN MON t ::: Nil, Bimodule s' t' p, Bimodule s' t' q)
    => p ~> q -> Mod (MOD p :: MODK kk s t) (MOD q)
instance (Bicategory kk, Ob0 kk (MONObj0 s), Ob0 kk (MONObj0 t)) => Profunctor (Mod :: CAT (MODK kk s t)) where
  dimap = dimapDefault
  r \\ Mod f = r \\ f
instance (Bicategory kk, Ob0 kk (MONObj0 s), Ob0 kk (MONObj0 t)) => Promonad (Mod :: CAT (MODK kk s t)) where
  id = Mod id
  Mod f . Mod g = Mod (f . g)
instance (Bicategory kk, Ob0 kk (MONObj0 s), Ob0 kk (MONObj0 t)) => CategoryOf (MODK kk s t) where
  type (~>) = Mod
  type Ob (p :: MODK kk s t) = (p ~ MOD (UNMOD p), Bimodule (UN MON s ::: Nil) (UN MON t ::: Nil) (UNMOD p), Ob (UNMOD p))

instance (Bicategory kk) => Bicategory (MODK kk) where
  type Ob0 (MODK kk) (s :: MONK kk) = (Monad (UN MON s :: kk (MONObj0 s) (MONObj0 s)), Ob0 kk (MONObj0 s))
  type I @(MODK kk) @i = MOD (UN MON i ::: Nil)
  type MOD p `O` MOD q = MOD (p `O` q)
  iObj :: forall (i :: MONK kk). (Ob0 (MODK kk) i) => Obj (I :: MODK kk i i)
  iObj = Mod id
  Mod f `o` Mod g = let fg = f `o` g in Mod fg
  -- leftUnitor (Mod p) = let lp = leftUnitor p in Mod lp \\ lp
