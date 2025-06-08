{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Product where

import Prelude (type (~))

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal(..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Preorder.ThinCategory (Codiscrete, Discrete (..), ThinProfunctor (..), anyArr)
import Proarrow.Profunctor.Representable (Representable (..))

type Fst :: (a, b) -> a
type family Fst a where
  Fst '(a, b) = a
type Snd :: (a, b) -> b
type family Snd a where
  Snd '(a, b) = b

type (:**:) :: j1 +-> k1 -> j2 +-> k2 -> (j1, j2) +-> (k1, k2)
data (c :**: d) a b where
  (:**:) :: { fstK :: c a1 b1, sndK :: d a2 b2 } -> (c :**: d) '(a1, a2) '(b1, b2)

instance (CategoryOf k1, CategoryOf k2) => CategoryOf (k1, k2) where
  type (~>) = (~>) :**: (~>)
  type Ob a = (a ~ '(Fst a, Snd a), Ob (Fst a), Ob (Snd a))

-- | The product promonad of promonads `p` and `q`.
instance (Promonad p, Promonad q) => Promonad (p :**: q) where
  id = id :**: id
  (f1 :**: f2) . (g1 :**: g2) = (f1 . g1) :**: (f2 . g2)

instance (Profunctor p, Profunctor q) => Profunctor (p :**: q) where
  dimap (l1 :**: l2) (r1 :**: r2) (f1 :**: f2) = dimap l1 r1 f1 :**: dimap l2 r2 f2
  r \\ (f :**: g) = r \\ f \\ g

instance (DaggerProfunctor p, DaggerProfunctor q) => DaggerProfunctor (p :**: q) where
  dagger (f :**: g) = dagger f :**: dagger g

instance (ThinProfunctor p, ThinProfunctor q) => ThinProfunctor (p :**: q) where
  type HasArrow (p :**: q) '(a1, a2) '(b1, b2) = (HasArrow p a1 b1, HasArrow q a2 b2)
  arr = arr :**: arr
  withArr (f :**: g) r = withArr f (withArr g r)

instance (Codiscrete p, Codiscrete q) => Codiscrete (p :**: q) where
  anyArr = anyArr :**: anyArr

instance (Discrete p, Discrete q) => Discrete (p :**: q) where
  withEq (f :**: g) r = withEq f (withEq g r)

instance (Representable p, Representable q) => Representable (p :**: q) where
  type (p :**: q) % '(a, b) = '(p % a, q % b)
  index (p :**: q) = index p :**: index q
  tabulate (f :**: g) = tabulate f :**: tabulate g
  repMap (f :**: g) = repMap @p f :**: repMap @q g

instance (MonoidalProfunctor p, MonoidalProfunctor q) => MonoidalProfunctor (p :**: q) where
  par0 = par0 :**: par0
  (f1 :**: f2) `par` (g1 :**: g2) = (f1 `par` g1) :**: (f2 `par` g2)

instance (Monoidal j, Monoidal k) => Monoidal (j, k) where
  type Unit = '(Unit, Unit)
  type '(a1, a2) ** '(b1, b2) = '(a1 ** b1, a2 ** b2)
  withOb2 @'(a1, a2) @'(b1, b2) r = withOb2 @j @a1 @b1 (withOb2 @k @a2 @b2 r)
  leftUnitor @'(a1, a2) = leftUnitor @j @a1 :**: leftUnitor @k @a2
  leftUnitorInv @'(a1, a2) = leftUnitorInv @j @a1 :**: leftUnitorInv @k @a2
  rightUnitor @'(a1, a2) = rightUnitor @j @a1 :**: rightUnitor @k @a2
  rightUnitorInv @'(a1, a2) = rightUnitorInv @j @a1 :**: rightUnitorInv @k @a2
  associator @'(a1, a2) @'(b1, b2) @'(c1, c2) = associator @j @a1 @b1 @c1 :**: associator @k @a2 @b2 @c2
  associatorInv @'(a1, a2) @'(b1, b2) @'(c1, c2) = associatorInv @j @a1 @b1 @c1 :**: associatorInv @k @a2 @b2 @c2

instance (SymMonoidal j, SymMonoidal k) => SymMonoidal (j, k) where
  swap @'(a1, a2) @'(b1, b2) = swap @j @a1 @b1 :**: swap @k @a2 @b2

instance (Strong m p, Strong m' q) => Strong (m, m') (p :**: q) where
  act (p :**: q) (x :**: y) = act p x :**: act q y
instance (MonoidalAction n j, MonoidalAction m k) => MonoidalAction (n, m) (j, k) where
  type Act '(p, q) '(x, y) = '(Act p x, Act q y)
  withObAct @'(p, q) @'(x, y) r = withObAct @n @j @p @x (withObAct @m @k @q @y r)
  unitor = unitor @n :**: unitor @m
  unitorInv = unitorInv @n :**: unitorInv @m
  multiplicator @'(p, q) @'(r, s) @'(x, y) = multiplicator @n @j @p @r @x :**: multiplicator @m @k @q @s @y
  multiplicatorInv @'(p, q) @'(r, s) @'(x, y) = multiplicatorInv @n @j @p @r @x :**: multiplicatorInv @m @k @q @s @y
