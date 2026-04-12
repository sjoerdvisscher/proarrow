module Proarrow.Optic where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Core (Profunctor (..), Promonad (..), CategoryOf (..), Kind, CAT, type (+->), dimapDefault)

type data OPTIC (j :: Kind) (k :: Kind) (c :: j +-> k -> Constraint) = OPT k j
type family OptL (p :: OPTIC j k c) where
  OptL (OPT j k) = j
type family OptR (p :: OPTIC j k c) where
  OptR (OPT j k) = k
type Optic_ :: CAT (OPTIC j k c)
data Optic_ ab st where
  Optic :: (Ob a, Ob b, Ob s, Ob t) => { over :: forall p. (c p) => p a b -> p s t } -> Optic_ (OPT a b :: OPTIC j k c) (OPT s t)

instance (CategoryOf j, CategoryOf k) => Profunctor (Optic_ :: CAT (OPTIC j k c)) where
  dimap = dimapDefault
  r \\ Optic{} = r
instance (CategoryOf j, CategoryOf k) => Promonad (Optic_ :: CAT (OPTIC j k c)) where
  id = Optic id
  Optic n . Optic m = Optic \p -> n (m p)
instance (CategoryOf j, CategoryOf k) => CategoryOf (OPTIC j k c) where
  type (~>) = Optic_
  type Ob opt = (opt ~ OPT (OptL opt) (OptR opt), Ob (OptL opt), Ob (OptR opt))

type Optic (c :: j +-> k -> Constraint) s t a b = Optic_ (OPT a b) (OPT s t :: OPTIC j k c)
type Optic' c s a = Optic c s s a a

class (c1 p, c2 p) => (c1 :&&: c2) p
instance (c1 p, c2 p) => (c1 :&&: c2) p
-- | Compose optics if different kinds
(%) :: Optic c1 s t a b -> Optic c2 a b c d -> Optic (c1 :&&: c2) s t c d
Optic n % Optic m = Optic (n . m)

type Iso s t a b = Optic Profunctor s t a b
type Iso' s a = Iso s s a a

iso :: forall {j} {k} (s :: k) (t :: j) a b. (CategoryOf j, CategoryOf k) => (s ~> a) -> (b ~> t) -> Iso s t a b
iso sa bt = Optic (dimap sa bt) \\ sa \\ bt

data Re p s t a b where
  Re :: (Ob a, Ob b) => {unRe :: p b a -> p t s} -> Re p s t a b

instance (Profunctor p) => Profunctor (Re p s t) where
  dimap l r (Re f) = Re (f . dimap r l) \\ l \\ r
  r \\ Re{} = r

class
  (forall p a b. (coc p) => c (Re p a b)) =>
  InvertableOptic (c :: j +-> k -> Constraint) (coc :: k +-> j -> Constraint)
    | c -> coc

instance InvertableOptic Profunctor Profunctor
instance (InvertableOptic l l', InvertableOptic r r') => InvertableOptic (l :&&: r) (l' :&&: r')

re :: (Ob a, Ob b, InvertableOptic c coc) => Optic c s t a b -> Optic coc b a t s
re (Optic l) = Optic (unRe (l (Re id)))
