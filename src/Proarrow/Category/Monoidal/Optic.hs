{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-orphans -fprint-potential-instances #-}

module Proarrow.Category.Monoidal.Optic where

import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Prelude (Either (..), Maybe (..), Monad (..), Traversable, const, either, fmap, uncurry, ($), type (~))

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.Nat ((!))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..), SymMonoidal, swap)
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..), composeActs, decomposeActs, actHom)
import Proarrow.Category.Opposite (OPPOSITE (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), dimapDefault, obj, type (+->))
import Proarrow.Core qualified as Core
import Proarrow.Functor (Prelude (..))
import Proarrow.Object (src, tgt)
import Proarrow.Object.BinaryCoproduct (COPROD (..), Coprod (..))
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Star (Star, pattern Star)

type Optic :: Kind -> c -> d -> c -> d -> Type
data Optic m a b s t where
  Optic
    :: forall {c} {d} {m} (x :: m) (x' :: m) a b s t
     . (Ob (a :: c), Ob (b :: d))
    => s ~> (x `Act` a)
    -> x ~> x'
    -> (x' `Act` b) ~> t
    -> Optic m a b s t

type IsOptic m c d = (MonoidalAction m c, MonoidalAction m d)

instance (CategoryOf c, CategoryOf d) => Profunctor (Optic m a b :: c +-> d) where
  dimap l r (Optic f w g) = Optic (f . l) w (r . g)
  r \\ Optic f _ g = r \\ f \\ g

instance (IsOptic m c d) => Strong m (Optic m a b :: c +-> d) where
  act :: forall (a1 :: m) (b1 :: m) (s :: d) (t :: c). a1 ~> b1 -> Optic m a b s t -> Optic m a b (Act a1 s) (Act b1 t)
  act w (Optic @x @x' f w' g) =
    Optic (composeActs @a1 @x @a (src w `actHom` src f) f) (w `par` w') (decomposeActs @b1 @x' @b g (tgt w `actHom` tgt g))
      \\ w
      \\ w'

type data OPTIC m (c :: Kind) (d :: Kind) = OPT c d
type family OptL (p :: OPTIC w c d) where
  OptL (OPT c d) = c
type family OptR (p :: OPTIC w c d) where
  OptR (OPT c d) = d
type OpticCat :: CAT (OPTIC w c d)
data OpticCat ab st where
  OpticCat :: Optic m a b s t -> OpticCat (OPT a b :: OPTIC m c d) (OPT s t)

instance (IsOptic m c d) => Profunctor (OpticCat :: CAT (OPTIC m c d)) where
  dimap = dimapDefault
  r \\ OpticCat (Optic f _ g) = r \\ f \\ g
instance (IsOptic m c d) => Promonad (OpticCat :: CAT (OPTIC m c d)) where
  id = OpticCat (prof2ex id)
  OpticCat l@Optic{} . OpticCat r@Optic{} = OpticCat $ prof2ex (ex2prof l . ex2prof r)

-- | The category of optics.
instance (IsOptic m c d) => CategoryOf (OPTIC m c d) where
  type (~>) = OpticCat
  type Ob a = (a ~ OPT (OptL a) (OptR a), Ob (OptL a), Ob (OptR a))

type MixedOptic m a b s t = Core.Optic (Strong m) s t a b

toIso :: MixedOptic () a b s t -> Core.Iso s t a b
toIso l p = l p

ex2prof :: forall m a b s t. Optic m a b s t -> MixedOptic m a b s t
ex2prof (Optic l w r) p = dimap l r (act w p)

prof2ex
  :: forall {c} {d} m (a :: c) (b :: d) (s :: c) (t :: d)
   . (MonoidalAction m c, MonoidalAction m d, Ob a, Ob b)
  => MixedOptic m a b s t
  -> Optic m a b s t
prof2ex p2p = p2p (Optic (unitorInv @m) par0 (unitor @m))

type Lens (s :: k) t a b = MixedOptic k a b s t
mkLens
  :: (Cartesian k, Act s a ~ (s && a), Act s b ~ (s && b), Ob (b :: k))
  => (s ~> a) -> ((s && b) ~> t) -> Lens s t a b
mkLens sa sbt = ex2prof (Optic (id &&& sa) (src sa) sbt) \\ sa

type Prism (s :: k) t a b = MixedOptic (COPROD k) a b s t
mkPrism :: (s -> Either t a) -> (b -> t) -> Prism s t a b
mkPrism sta bt = ex2prof @(COPROD Type) (Optic sta id (either id bt))

type Traversal s t a b = MixedOptic (SUBCAT Traversable) a b s t
traversing :: (Traversable f) => Traversal (f a) (f b) a b
traversing = ex2prof @(SUBCAT Traversable) (Optic Prelude id unPrelude)

class (Monad m) => Algebra m a where algebra :: m a -> a
instance (Monad m) => Algebra m (m a) where algebra = (>>= id)
instance (Monad m) => Algebra m () where algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where
  algebra mab = (algebra (fmap fst mab), algebra (fmap snd mab))

type AlgebraicLens m s t a b = MixedOptic (SUBCAT (Algebra m)) a b s t
mkAlgebraicLens :: forall m s t a b. (Monad m) => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u = ex2prof @(SUBCAT (Algebra m)) (Optic (\s -> (return @m s, v s)) id (uncurry u))

newtype Viewing a (b :: Type) s (t :: Type) = Viewing {unView :: s -> a}
instance Profunctor (Viewing a b) where
  dimap l _ (Viewing f) = Viewing (f . l)
instance Strong Type (Viewing a b) where
  act _ (Viewing f) = Viewing (f . snd)

infixl 8 ^.
(^.) :: s -> (Viewing a b a b -> Viewing a b s t) -> a
(^.) s l = unView (l $ Viewing id) s

data Previewing a (b :: Type) s (t :: Type) where
  Previewing :: {unPreview :: s -> Maybe a} -> Previewing a b s t
instance Profunctor (Previewing a b) where
  dimap l _ (Previewing f) = Previewing (f . l)
  r \\ Previewing f = r \\ f
instance Strong (COPROD Type) (Previewing a b) where
  act _ (Previewing f) = Previewing (either (const Nothing) f)
instance Strong Type (Previewing a b) where
  act _ (Previewing f) = Previewing (f . snd)

infixl 8 ?.
(?.)
  :: s -> (Previewing a b a b -> Previewing a b s t) -> Maybe a
(?.) s l = unPreview (l $ Previewing Just) s

type KlCat m = KLEISLI (Star (Prelude m))
data Updating a b s t where
  Update :: {unUpdate :: b -> s -> m t} -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m)
instance (Monad m) => Profunctor (Updating a b :: KlCat m +-> Type) where
  dimap l (Kleisli (Star r)) (Update u) = Update (\b x -> u b (l x) >>= unPrelude . r)
  r \\ Update u = r \\ u
instance (Monad m) => Strong Type (Updating a b :: KlCat m +-> Type) where
  act f (Update u) = Update (\b (a, x) -> (f a,) `fmap` u b x)

mupdate
  :: (Monad m)
  => (Updating a (KL b :: KlCat m) a (KL b :: KlCat m) -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m))
  -> b
  -> s
  -> m t
mupdate f = unUpdate $ f (Update (\b _ -> return b))

newtype Replacing a b s t = Replace {unReplace :: (a -> b) -> (s -> t)}
instance Profunctor (Replacing a b) where
  dimap l r (Replace f) = Replace (\ab -> r . f ab . l)
instance Strong Type (Replacing a b) where
  act w (Replace f) = Replace (\u -> bimap w (f u))
instance Strong (COPROD Type) (Replacing a b) where
  act (Coprod (Id w)) (Replace f) = Replace (\u -> bimap w (f u))
instance Strong (Type -> Type) (Replacing a b) where
  act w (Replace f) = Replace (\g -> w ! f g)

infixl 8 %~
(%~) :: (Replacing a b a b -> Replacing a b s t) -> (a -> b) -> (s -> t)
(%~) l = unReplace (l $ Replace id)

infixl 8 .~
(.~) :: (Replacing a b a b -> Replacing a b s t) -> b -> s -> t
l .~ b = l %~ const b

newtype Classifying m a b s t = Classifying
  {unClassify :: (Monad m) => m s -> b -> t}
instance (Monad m) => Profunctor (Classifying m a b) where
  dimap l r (Classifying f) = Classifying (\u -> r . f (fmap l u))
instance (Monad m) => Strong (SUBCAT (Algebra m)) (Classifying m a b) where
  act (Sub w) (Classifying f) = Classifying (\m b -> (algebra (fmap (w . fst) m), f (fmap snd m) b))

infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = unClassify (l $ Classifying (const id)) ms b

-- Charts, a kind of dual to optics.
type IsChart m c d = (IsOptic m c d, SymMonoidal m)

type data CHART m (c :: Kind) (d :: Kind) = CHA c (OPPOSITE d)
type family ChaL (p :: CHART w c d) where
  ChaL (CHA c d) = c
type family ChaR (p :: CHART w c d) where
  ChaR (CHA c d) = d
type ChartCat :: CAT (CHART w c d)
data ChartCat ab st where
  ChartCat :: Optic m a t s b -> ChartCat (CHA a (OP b) :: CHART m c d) (CHA s (OP t))

instance (IsChart m c d) => Profunctor (ChartCat :: CAT (CHART m c d)) where
  dimap = dimapDefault
  r \\ ChartCat (Optic f _ g) = r \\ f \\ g
instance (IsChart m c d) => Promonad (ChartCat :: CAT (CHART m c d)) where
  id = ChartCat (prof2ex id)
  ChartCat (Optic @x @x' @_ @t ll lw lr) . ChartCat (Optic @y @y' @a rl rw rr) =
    ChartCat $
      Optic (composeActs @x @y @a ll rl) (lw `par` rw) (decomposeActs @y' @x' @t lr rr . (swap @_ @x' @y' `actHom` obj @t))
        \\ lw
        \\ rw

-- | The category of charts.
instance (IsChart m c d) => CategoryOf (CHART m c d) where
  type (~>) = ChartCat
  type Ob a = (a ~ CHA (ChaL a) (ChaR a), Ob (ChaL a), Ob (ChaR a))
