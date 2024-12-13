{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Product where

import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, swap')
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..), Codiscrete, anyArr, Discrete (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Category.Dagger (DaggerProfunctor (..))

type Fst :: (a, b) -> a
type family Fst a where
  Fst '(a, b) = a
type Snd :: (a, b) -> b
type family Snd a where
  Snd '(a, b) = b

type (:**:) :: j1 +-> k1 -> j2 +-> k2 -> (j1, j2) +-> (k1, k2)
data (c :**: d) a b where
  (:**:) :: c a1 b1 -> d a2 b2 -> (c :**: d) '(a1, a2) '(b1, b2)

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
  leftUnitor @'(a1, a2) = leftUnitor @j @a1 :**: leftUnitor @k @a2
  leftUnitorInv @'(a1, a2) = leftUnitorInv @j @a1 :**: leftUnitorInv @k @a2
  rightUnitor @'(a1, a2) = rightUnitor @j @a1 :**: rightUnitor @k @a2
  rightUnitorInv @'(a1, a2) = rightUnitorInv @j @a1 :**: rightUnitorInv @k @a2
  associator @'(a1, a2) @'(b1, b2) @'(c1, c2) = associator @j @a1 @b1 @c1 :**: associator @k @a2 @b2 @c2
  associatorInv @'(a1, a2) @'(b1, b2) @'(c1, c2) = associatorInv @j @a1 @b1 @c1 :**: associatorInv @k @a2 @b2 @c2

instance (SymMonoidal j, SymMonoidal k) => SymMonoidal (j, k) where
  swap' (a1 :**: a2) (b1 :**: b2) = swap' a1 b1 :**: swap' a2 b2
