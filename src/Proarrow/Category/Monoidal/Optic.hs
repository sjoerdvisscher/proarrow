{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal.Optic where

import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Prelude (Either, Maybe (..), Monad (..), Traversable, const, either, fmap, fst, snd, uncurry, ($), type (~))

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.Nat (Nat (..), (!))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..), SymMonoidal, swap)
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..), composeActs, decomposeActs)
import Proarrow.Category.Opposite (OPPOSITE (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, PRO, Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Functor (Prelude (..))
import Proarrow.Object (src, tgt)
import Proarrow.Object.BinaryCoproduct (COPROD (..), Coprod (..))
import Proarrow.Object.BinaryProduct ()
import Proarrow.Profunctor.Star (Star (..))

type Optic :: PRO m m' -> c -> d -> c -> d -> Type
data Optic w a b s t where
  Optic
    :: forall {c} {d} {m} {m'} (x :: m) (x' :: m') a b s t w
     . (Ob (a :: c), Ob (b :: d))
    => s ~> (x `Act` a)
    -> w x x'
    -> (x' `Act` b) ~> t
    -> Optic (w :: PRO m m') a b s t

type IsOptic (w :: PRO m m') c d = (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d)

instance (CategoryOf c, CategoryOf d) => Profunctor (Optic w a b :: PRO c d) where
  dimap l r (Optic f w g) = Optic (f . l) w (r . g)
  r \\ Optic f _ g = r \\ f \\ g

instance (IsOptic w c d) => Strong (w :: PRO m m') (Optic w a b :: PRO c d) where
  act :: forall (a1 :: m) (b1 :: m') (s :: c) (t :: d). w a1 b1 -> Optic w a b s t -> Optic w a b (Act a1 s) (Act b1 t)
  act w (Optic @x @x' f w' g) =
    Optic (composeActs @a1 @x @a (src w `act` src f) f) (w `par` w') (decomposeActs @b1 @x' @b g (tgt w `act` tgt g))
      \\ w
      \\ w'

parallel :: Optic w a b s t -> Optic w' c d u v -> Optic (w :**: w') '(a, c) '(b, d) '(s, u) '(t, v)
parallel (Optic f w g) (Optic h w' i) = Optic (f :**: h) (w :**: w') (g :**: i)

type data OPTIC (w :: PRO m m') (c :: Kind) (d :: Kind) = OPT c d
type family OptL (p :: OPTIC w c d) where
  OptL (OPT c d) = c
type family OptR (p :: OPTIC w c d) where
  OptR (OPT c d) = d
type OpticCat :: CAT (OPTIC w c d)
data OpticCat ab st where
  OpticCat :: Optic w a b s t -> OpticCat (OPT a b :: OPTIC w c d) (OPT s t)

instance (IsOptic w c d) => Profunctor (OpticCat :: CAT (OPTIC w c d)) where
  dimap = dimapDefault
  r \\ OpticCat (Optic f _ g) = r \\ f \\ g
instance (IsOptic w c d) => Promonad (OpticCat :: CAT (OPTIC w c d)) where
  id = OpticCat (prof2ex id)
  OpticCat l@Optic{} . OpticCat r@Optic{} = OpticCat $ prof2ex (ex2prof l . ex2prof r)
instance (IsOptic w c d) => CategoryOf (OPTIC w c d) where
  type (~>) = OpticCat
  type Ob a = (a ~ OPT (OptL a) (OptR a), Ob (OptL a), Ob (OptR a))

type ProfOptic w a b s t = forall p. (Strong w p) => p a b -> p s t
type MixedOptic m a b s t = ProfOptic ((~>) @m) a b s t

ex2prof :: forall w a b s t. Optic w a b s t -> ProfOptic w a b s t
ex2prof (Optic l w r) p = dimap l r (act w p)

prof2ex
  :: forall {c} {d} m m' w a b s t
   . (MonoidalProfunctor w, MonoidalAction m c, MonoidalAction m' d, Ob a, Ob b)
  => ProfOptic (w :: PRO m m') (a :: c) (b :: d) (s :: c) (t :: d)
  -> Optic w a b s t
prof2ex p2p = p2p (Optic (unitorInv @m) par0 (unitor @m'))

type Lens s t a b = MixedOptic Type a b s t
mkLens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
mkLens sa sbt = ex2prof (Optic (\s -> (s, sa s)) (src sa) (uncurry sbt))

type Prism s t a b = MixedOptic (COPROD Type) (COPR a) (COPR b) (COPR s) (COPR t)
mkPrism :: (s -> Either t a) -> (b -> t) -> Prism s t a b
mkPrism sat bt = ex2prof (Optic (Coprod sat) (Coprod (tgt bt)) (Coprod (either id bt)))

type Traversal s t a b = MixedOptic (Type -> Type) a b s t
traversing :: (Traversable f) => Traversal (f a) (f b) a b
traversing = ex2prof @((~>) @(Type -> Type)) (Optic Prelude id unPrelude)

class (Monad m) => Algebra m a where algebra :: m a -> a
instance (Monad m) => Algebra m (m a) where algebra = (>>= id)
instance (Monad m) => Algebra m () where algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where
  algebra mab = (algebra (fmap fst mab), algebra (fmap snd mab))

type AlgebraicLens m s t a b = MixedOptic (SUBCAT (Algebra m)) a b s t
mkAlgebraicLens :: forall m s t a b. (Monad m) => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u = ex2prof @((~>) @(SUBCAT (Algebra m))) (Optic (\s -> (return @m s, v s)) (Sub obj) (uncurry u))

newtype Viewing a (b :: Type) s (t :: Type) = Viewing {unView :: s -> a}
instance Profunctor (Viewing a b) where
  dimap l _ (Viewing f) = Viewing (f . l)
instance Strong (->) (Viewing a b) where
  act _ (Viewing f) = Viewing (f . snd)

infixl 8 ^.
(^.) :: s -> (Viewing a b a b -> Viewing a b s t) -> a
(^.) s l = unView (l $ Viewing id) s

data Previewing a (b :: COPROD Type) s (t :: COPROD Type) where
  Previewing :: {unPreview :: s -> Maybe a} -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)
instance Profunctor (Previewing a b) where
  dimap (Coprod l) Coprod{} (Previewing f) = Previewing (f . l)
  r \\ Previewing f = r \\ f
instance Strong (Coprod (->)) (Previewing a b) where
  act _ (Previewing f) = Previewing (either (const Nothing) f)
instance Strong (->) (Previewing a b) where
  act _ (Previewing f) = Previewing (f . snd)

infixl 8 ?.
(?.)
  :: s -> (Previewing (COPR a) (COPR b) (COPR a) (COPR b) -> Previewing (COPR a) (COPR b) (COPR s) (COPR t)) -> Maybe a
(?.) s l = unPreview (l $ Previewing Just) s

newtype Setting a b s t = Setting {unSet :: (a -> b) -> (s -> t)}
instance Profunctor (Setting a b) where
  dimap l r (Setting f) = Setting (\u -> r . f u . l)
instance Strong (->) (Setting a b) where
  act w (Setting f) = Setting (\u -> bimap w (f u))
instance Strong (Coprod (->)) (Setting a b) where
  act (Coprod w) (Setting f) = Setting (\u -> bimap w (f u))

infixl 8 .~
(.~) :: (Setting a b a b -> Setting a b s t) -> b -> s -> t
(.~) l b = unSet (l $ Setting id) (const b)

type KlCat m = KLEISLI (Star (Prelude m))
data Updating a b s t where
  Update :: {unUpdate :: b -> s -> m t} -> Updating a (KL b :: KlCat m) s (KL t :: KlCat m)
instance (Monad m) => Profunctor (Updating a b :: PRO Type (KlCat m)) where
  dimap l (Kleisli (Star r)) (Update u) = Update (\b x -> u b (l x) >>= unPrelude . r)
  r \\ Update u = r \\ u
instance (Monad m) => Strong (->) (Updating a b :: PRO Type (KlCat m)) where
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
instance Strong (->) (Replacing a b) where
  act w (Replace f) = Replace (\u -> bimap w (f u))
instance Strong (Coprod (->)) (Replacing a b) where
  act (Coprod w) (Replace f) = Replace (\u -> bimap w (f u))
instance Strong (Nat :: CAT (Type -> Type)) (Replacing a b) where
  act w (Replace f) = Replace (\g -> w ! f g)

infixl 8 %~
(%~) :: (Replacing a b a b -> Replacing a b s t) -> (a -> b) -> (s -> t)
(%~) l = unReplace (l $ Replace id)

newtype Classifying m a b s t = Classifying
  {unClassify :: (Monad m) => m s -> b -> t}
instance (Monad m) => Profunctor (Classifying m a b) where
  dimap l r (Classifying f) = Classifying (\u -> r . f (fmap l u))
instance (Monad m) => Strong (Sub (->) :: CAT (SUBCAT (Algebra m))) (Classifying m a b) where
  act (Sub w) (Classifying f) = Classifying (\m b -> (algebra (fmap (w . fst) m), f (fmap snd m) b))

infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = unClassify (l $ Classifying (const id)) ms b

-- Charts, a kind of dual to optics.
type IsChart (w :: PRO m m') c d = (IsOptic w c d, SymMonoidal m')

type data CHART (w :: PRO m m') (c :: Kind) (d :: Kind) = CHA c (OPPOSITE d)
type family ChaL (p :: CHART w c d) where
  ChaL (CHA c d) = c
type family ChaR (p :: CHART w c d) where
  ChaR (CHA c d) = d
type ChartCat :: CAT (CHART w c d)
data ChartCat ab st where
  ChartCat :: Optic w a t s b -> ChartCat (CHA a (OP b) :: CHART w c d) (CHA s (OP t))

instance (IsChart w c d) => Profunctor (ChartCat :: CAT (CHART w c d)) where
  dimap = dimapDefault
  r \\ ChartCat (Optic f _ g) = r \\ f \\ g
instance (IsChart w c d) => Promonad (ChartCat :: CAT (CHART (w :: PRO m m') c d)) where
  id = ChartCat (prof2ex id)
  ChartCat (Optic @x @x' @_ @t ll lw lr) . ChartCat (Optic @y @y' @a rl rw rr) =
    ChartCat $
      Optic (composeActs @x @y @a ll rl) (lw `par` rw) (decomposeActs @y' @x' @t lr rr . (swap @x' @y' `act` obj @t))
        \\ lw
        \\ rw
instance (IsChart w c d) => CategoryOf (CHART w c d) where
  type (~>) = ChartCat
  type Ob a = (a ~ CHA (ChaL a) (ChaR a), Ob (ChaL a), Ob (ChaR a))
