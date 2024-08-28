{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Product where

import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, swap')
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Profunctor.Representable (Representable (..))

type Fst :: (a, b) -> a
type family Fst a where
  Fst '(a, b) = a
type Snd :: (a, b) -> b
type family Snd a where
  Snd '(a, b) = b

type (:**:) :: CAT k1 -> CAT k2 -> CAT (k1, k2)
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
  leftUnitor (a1 :**: a2) = leftUnitor a1 :**: leftUnitor a2
  leftUnitorInv (a1 :**: a2) = leftUnitorInv a1 :**: leftUnitorInv a2
  rightUnitor (a1 :**: a2) = rightUnitor a1 :**: rightUnitor a2
  rightUnitorInv (a1 :**: a2) = rightUnitorInv a1 :**: rightUnitorInv a2
  associator (a1 :**: a2) (b1 :**: b2) (c1 :**: c2) = associator a1 b1 c1 :**: associator a2 b2 c2
  associatorInv (a1 :**: a2) (b1 :**: b2) (c1 :**: c2) = associatorInv a1 b1 c1 :**: associatorInv a2 b2 c2

instance (SymMonoidal j, SymMonoidal k) => SymMonoidal (j, k) where
  swap' (a1 :**: a2) (b1 :**: b2) = swap' a1 b1 :**: swap' a2 b2
