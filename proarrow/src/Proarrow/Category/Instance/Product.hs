{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __product of two categories__: the tuple kind @(j, k)@ is the category whose arrows are
-- pairs of arrows, @p ':**:' q@ being the corresponding product of profunctors. The projections
-- 'Fst'\/'Snd' and diagonal 'Diag' are provided as representable profunctors.
module Proarrow.Category.Instance.Product where

import Prelude (type (~))

import Data.Type.Nat (SNat (..), snat)

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin
  ( CodiscreteProfunctor (..)
  , Discrete (..)
  , Enumerable (..)
  , Finite (..)
  , Indexed (..)
  , ThinProfunctor (..)
  )
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))

type (:**:) :: j1 +-> k1 -> j2 +-> k2 -> (j1, j2) +-> (k1, k2)
data (c :**: d) a b where
  (:**:) :: {fstK :: c a1 b1, sndK :: d a2 b2} -> (c :**: d) '(a1, a2) '(b1, b2)

-- | The product of two categories.
instance (CategoryOf k1, CategoryOf k2) => CategoryOf (k1, k2) where
  type (~>) = (~>) :**: (~>)
  type Ob a = (a ~ '(Fst @ a, Snd @ a), Ob (Fst @ a), Ob (Snd @ a))

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

data family Fst :: (j, k) +-> j
instance (CategoryOf j, CategoryOf k) => FunctorForRep (Fst :: (j, k) +-> j) where
  type Fst @ '(a, b) = a
  fmap (f :**: _) = f

data family Snd :: (j, k) +-> k
instance (CategoryOf j, CategoryOf k) => FunctorForRep (Snd :: (j, k) +-> k) where
  type Snd @ '(a, b) = b
  fmap (_ :**: f) = f

data family Diag :: k +-> (k, k)
instance (CategoryOf k) => FunctorForRep (Diag :: k +-> (k, k)) where
  type Diag @ a = '(a, a)
  fmap f = f :**: f

checkDiscrete :: (Discrete j, Discrete k) => Hom (j, k) a b -> ((a ~ b) => r) -> r
checkDiscrete f r = withEq f r

-- Does not work
-- checkDiscreteProfunctor :: (DiscreteProfunctor p, DiscreteProfunctor q) => (p :**: q) a b -> r
-- checkDiscreteProfunctor f = exfalso f

checkCodiscreteProfunctor :: (CodiscreteProfunctor p, CodiscreteProfunctor q, Ob a, Ob b) => (p :**: q) a b
checkCodiscreteProfunctor = anyArr

-- | The product of two enumerable kinds is enumerable, but numbering one in general needs type-level
-- division to invert the pairing, which @fin@ does not provide, so this instance for
-- @(BOOL, BOOL)@ is numbered by hand. The order matches the value-level
-- 'Proarrow.Category.Enriched.Finitary.pairIndex' convention: first component slowest.
--
-- ("Proarrow.Category.Sheaf" uses this kind as the opens of a discrete two-point space: a pair of
-- booleans is a subset of @{x, y}@.)
instance Indexed (BOOL, BOOL)

instance Finite (BOOL, BOOL) where
  type Objects (BOOL, BOOL) = '[ '(FLS, FLS), '(FLS, TRU), '(TRU, FLS), '(TRU, TRU)]

instance Enumerable (BOOL, BOOL) where
  withIndex @a r = case obj @a of
    Fls :**: Fls -> r
    Fls :**: Tru -> r
    Tru :**: Fls -> r
    Tru :**: Tru -> r
  withOb @a r = case snat @(Index a) of
    SZ -> r
    SS @i -> case snat @i of
      SZ -> r
      SS @i' -> case snat @i' of
        SZ -> r
        SS @i'' -> case snat @i'' of SZ -> r
