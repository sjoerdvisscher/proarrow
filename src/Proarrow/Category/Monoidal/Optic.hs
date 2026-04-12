{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-orphans -fprint-potential-instances #-}

module Proarrow.Category.Monoidal.Optic where

import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Prelude (Maybe (..), Monad (..), Traversable, const, either, fmap, uncurry, ($), type (~))

import Data.Monoid qualified as P
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.Nat ((!))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, obj2, swap)
import Proarrow.Category.Monoidal.Action
  ( Costrong (..)
  , MonoidalAction (..)
  , SelfAction
  , Strong (..)
  , composeActs
  , decomposeActs
  , fromSelfAct
  )
import Proarrow.Category.Monoidal.Distributive qualified as Dist
import Proarrow.Category.Opposite (OPPOSITE (..))
import Proarrow.Core
  ( Any
  , CAT
  , CategoryOf (..)
  , Kind
  , OB
  , Profunctor (..)
  , Promonad (..)
  , UN
  , dimapDefault
  , obj
  , rmap
  , (//)
  , type (+->)
  )
import Proarrow.Functor (Prelude (..))
import Proarrow.Object (src, tgt)
import Proarrow.Object.BinaryCoproduct (COPROD (..), Coprod (..), HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..), HasProducts, PROD, Prod (..))
import Proarrow.Optic (InvertableOptic, Optic, Optic_ (..), Re (..))
import Proarrow.Profunctor.Constant (Constant)
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), withRepOb)
import Proarrow.Profunctor.Star (Star, pattern Star)

type ExOptic :: Kind -> c -> d -> c -> d -> Type
data ExOptic m a b s t where
  ExOptic
    :: forall {c} {d} {m} (x :: m) (x' :: m) a b s t
     . (Ob (a :: c), Ob (b :: d))
    => s ~> (x `Act` a)
    -> x ~> x'
    -> (x' `Act` b) ~> t
    -> ExOptic m a b s t

type IsOptic m c d = (MonoidalAction m c, MonoidalAction m d)

instance (CategoryOf c, CategoryOf d) => Profunctor (ExOptic m a b :: c +-> d) where
  dimap l r (ExOptic f w g) = ExOptic (f . l) w (r . g)
  r \\ ExOptic f _ g = r \\ f \\ g

instance (IsOptic m c d) => Strong m (ExOptic m a b :: c +-> d) where
  act
    :: forall (a1 :: m) (b1 :: m) (s :: d) (t :: c). a1 ~> b1 -> ExOptic m a b s t -> ExOptic m a b (Act a1 s) (Act b1 t)
  act w (ExOptic @x @x' f w' g) =
    ExOptic (composeActs @a1 @x @a (src w `act` src f) f) (w `par` w') (decomposeActs @b1 @x' @b g (tgt w `act` tgt g))
      \\ w
      \\ w'

ex2prof
  :: forall {c} {d} m (a :: c) (b :: d) s t. (CategoryOf c, CategoryOf d) => ExOptic m a b s t -> Optic (Strong m) s t a b
ex2prof (ExOptic l w r) = Optic (dimap l r . act w) \\ l \\ r

prof2ex
  :: forall {c} {d} m (a :: c) (b :: d) (s :: c) (t :: d)
   . (IsOptic m c d, Ob a, Ob b)
  => Optic (Strong m) s t a b
  -> ExOptic m a b s t
prof2ex p2p = over p2p (ExOptic (unitorInv @m) par0 (unitor @m))

type MonoidalOptic (s :: k) (t :: k) a b = Optic (Strong (SUBCAT (Any :: OB k))) s t a b
mkMonoidal
  :: forall {k} (m :: k) (a :: k) (b :: k) s t
   . (Monoidal k, Ob m, Ob a, Ob b) => (s ~> m ** a) -> (m ** b ~> t) -> MonoidalOptic s t a b
mkMonoidal sma mbt = ex2prof (ExOptic sma (Sub @(Any :: OB k) (obj @m)) mbt)

_1 :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => MonoidalOptic (a ** c) (b ** c) a b
_1 = mkMonoidal @c (swap @k @a @c) (swap @k @c @b)

_2 :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => MonoidalOptic (c ** a) (c ** b) a b
_2 = mkMonoidal @c (obj2 @c @a) (obj2 @c @b)

instance
  (Cartesian k, Ob c, Strong (SUBCAT (Any :: OB k)) ((~>) :: CAT k))
  => Strong (SUBCAT (Any :: OB k)) (Rep (Constant c) :: k +-> k)
  where
  act @m @m' @x @y g (Rep f) = withOb2 @k @(UN SUB m') @y (Rep (f . snd @k @(UN SUB m) @x)) \\ g \\ f
instance (Cartesian k, SelfAction k, Ob c) => Strong k (Rep (Constant c) :: k +-> k) where
  act @m @m' @x @y g (Rep f) = withObAct @k @k @m' @y (Rep (f . snd @k @m @x . fromSelfAct @m @x)) \\ g \\ f
instance Strong (COPROD Type) (Rep (Constant (P.First c)) :: Type +-> Type) where
  act _ (Rep f) = Rep (either (const (P.First Nothing)) f)

type Lens (s :: k) (t :: k) a b = Optic (Strong (PROD k)) s t a b
mkLens :: forall {k} (s :: k) (t :: k) a b. (HasProducts k, Ob b) => (s ~> a) -> ((s && b) ~> t) -> Lens s t a b
mkLens sa sbt = ex2prof (ExOptic (id &&& sa) (Prod (src sa)) sbt) \\ sa

type Prism (s :: k) t a b = Optic (Strong (COPROD k)) s t a b
mkPrism :: forall {k} (s :: k) (t :: k) a b. (HasCoproducts k, Ob a) => (s ~> (t || a)) -> (b ~> t) -> Prism s t a b
mkPrism sta bt = ex2prof (ExOptic sta (Coprod (Id (tgt bt))) (id ||| bt)) \\ bt

type HaskTraversal s t a b = Optic (Strong (SUBCAT Traversable)) s t a b
traversing :: (Traversable f) => HaskTraversal (f a) (f b) a b
traversing = ex2prof @(SUBCAT Traversable) (ExOptic Prelude id unPrelude)

type Traversal s t a b = Optic Dist.StrongDistributiveProfunctor s t a b
traversing' :: forall t a b. (Dist.Traversable t, Representable t, Ob a, Ob b) => Traversal (t % a) (t % b) a b
traversing' = withRepOb @t @a $ withRepOb @t @b $ Optic (Dist.repTraverse @t)

class (Monad m) => Algebra m a where algebra :: m a -> a
instance (Monad m) => Algebra m (m a) where algebra = (>>= id)
instance (Monad m) => Algebra m () where algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where
  algebra mab = (algebra (fmap fst mab), algebra (fmap snd mab))

type AlgebraicLens m s t a b = Optic (Strong (SUBCAT (Algebra m))) s t a b
mkAlgebraicLens :: forall m s t a b. (Monad m) => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u = ex2prof @(SUBCAT (Algebra m)) (ExOptic (\s -> (return @m s, v s)) id (uncurry u))

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

instance InvertableOptic (Strong m) (Costrong m)
instance InvertableOptic (Costrong m) (Strong m)
instance (Strong m p) => Costrong m (Re p s t) where
  coact @a (Re f) = Re \pyx -> f (act (obj @a) pyx)
instance (Costrong m p) => Strong m (Re p s t) where
  act @a @b @x @y g (Re f) = g //
    withObAct @m @_ @a @x $
      withObAct @m @_ @b @y $
        Re \payax -> f (coact @_ @_ @b (rmap (act g (obj @x)) payax))

-- Charts, a kind of dual to optics.
type IsChart m c d = (IsOptic m c d, SymMonoidal m)

type data CHART m (c :: Kind) (d :: Kind) = CHA c (OPPOSITE d)
type family ChaL (p :: CHART w c d) where
  ChaL (CHA c d) = c
type family ChaR (p :: CHART w c d) where
  ChaR (CHA c d) = d
type ChartCat :: CAT (CHART w c d)
data ChartCat ab st where
  ChartCat :: ExOptic m a t s b -> ChartCat (CHA a (OP b) :: CHART m c d) (CHA s (OP t))

instance (IsChart m c d) => Profunctor (ChartCat :: CAT (CHART m c d)) where
  dimap = dimapDefault
  r \\ ChartCat (ExOptic f _ g) = r \\ f \\ g
instance (IsChart m c d) => Promonad (ChartCat :: CAT (CHART m c d)) where
  id = ChartCat (prof2ex id)
  ChartCat (ExOptic @x @x' @_ @t ll lw lr) . ChartCat (ExOptic @y @y' @a rl rw rr) =
    ChartCat $
      ExOptic (composeActs @x @y @a ll rl) (lw `par` rw) (decomposeActs @y' @x' @t lr rr . (swap @_ @x' @y' `act` obj @t))
        \\ lw
        \\ rw

-- | The category of charts.
instance (IsChart m c d) => CategoryOf (CHART m c d) where
  type (~>) = ChartCat
  type Ob a = (a ~ CHA (ChaL a) (ChaR a), Ob (ChaL a), Ob (ChaR a))
