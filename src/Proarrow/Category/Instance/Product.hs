module Proarrow.Category.Instance.Product where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)

type Fst :: (a, b) -> a
type family Fst a where Fst '(a, b) = a
type Snd :: (a, b) -> b
type family Snd a where Snd '(a, b) = b

type (:**:) :: CAT k1 -> CAT k2 -> CAT (k1, k2)
data (c :**: d) a b where
  (:**:) :: c a1 b1 -> d a2 b2 -> (c :**: d) '(a1, a2) '(b1, b2)

type instance (~>) = (~>) :**: (~>)

-- | The product category of categories `c` and `d`.
instance (Category c, Category d) => Category (c :**: d) where
  type Ob a = (a ~ '(Fst a, Snd a), Ob (Fst a), Ob (Snd a))
  id = id :**: id
  (f1 :**: f2) . (g1 :**: g2) = (f1 . g1) :**: (f2 . g2)

instance (Category c, Category d) => Profunctor (c :**: d) where
  dimap = dimapDefault
  r \\ (f :**: g) = r \\ f \\ g