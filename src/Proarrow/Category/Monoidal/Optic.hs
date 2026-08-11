{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-orphans -fprint-potential-instances #-}

module Proarrow.Category.Monoidal.Optic where

import Data.Kind (Type)
import Data.Monoid qualified as P
import GHC.Generics qualified as G
import Prelude (Either (..), Maybe (..), Monad (..), const, either, flip, fmap, uncurry, ($))
import Prelude qualified as P

import Data.Functor.Const (Const (..))
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.Nat (ApplyAction)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, Tensor, obj2, swap)
import Proarrow.Category.Monoidal.Action
  ( Act
  , CoprodAction
  , MonoidalAction (..)
  , ProdAction
  , SubAction
  , composeActs
  , decomposeActs
  )
import Proarrow.Category.Monoidal.Distributive qualified as Dist
import Proarrow.Category.Monoidal.Strength (Costrong (..), Strong (..), strongId)
import Proarrow.Colimit.BinaryCoproduct (COPROD (..), HasBinaryCoproducts (..), HasCoproducts, nil, (++))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, type (+->))
import Proarrow.Functor (FromProfunctor (..), Functor (map), Prelude (..))
import Proarrow.Limit.BinaryProduct (Cartesian, HasBinaryProducts (..), HasProducts, PROD (..))
import Proarrow.Optic (InvertableOptic, Optic, Optic_ (..), Re (..), (:&&:))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), repObj, withObRep)

type ExOptic :: (m, k) +-> k -> k -> k -> k -> k -> Type
data ExOptic act a b s t where
  ExOptic
    :: forall {k} {m} {act} (x :: m) s t a b
     . (Ob (a :: k), Ob (b :: k), Ob x)
    => s ~> Act act x a
    -> Act act x b ~> t
    -> ExOptic act a b s t

instance (CategoryOf k) => Profunctor (ExOptic act a b :: k +-> k) where
  dimap l r (ExOptic @x f g) = ExOptic @x (f . l) (r . g)
  r \\ ExOptic f g = r \\ f \\ g
instance (MonoidalAction act) => Strong act (ExOptic act a b :: k +-> k) where
  act @z (ExOptic @x @s @t f g) =
    withOb2 @_ @z @x $
      ExOptic @(z ** x)
        (composeActs @act @z @x @a (repObj @act @'(z, s)) f)
        (decomposeActs @act @z @x @b g (repObj @act @'(z, t)))
        \\ f
        \\ g

ex2prof
  :: forall {k} {m} {act :: (m, k) +-> k} (a :: k) (b :: k) (s :: k) (t :: k)
   . (CategoryOf k, CategoryOf m, MonoidalAction act)
  => ExOptic act a b s t -> Optic (Strong act) s t a b
ex2prof (ExOptic @x l r) = Optic (dimap l r . act @act @_ @x) \\ l \\ r

prof2ex
  :: forall {k} {m} {act} (a :: k) (b :: k) (s :: k) (t :: k)
   . (CategoryOf k, CategoryOf m, MonoidalAction act)
  => Optic (Strong act) s t a b -> ExOptic act a b s t
prof2ex p2p@Optic{} = over p2p (ExOptic @Unit (unitorInv @act) (unitor @act))

type MonoidalOptic (s :: k) (t :: k) a b = Optic (Strong Tensor) s t a b
mkMonoidal
  :: forall {k} (m :: k) (a :: k) (b :: k) s t
   . (Monoidal k, Ob m, Ob a, Ob b) => (s ~> m ** a) -> (m ** b ~> t) -> MonoidalOptic s t a b
mkMonoidal sma mbt = ex2prof (ExOptic @m sma mbt)

_1 :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => MonoidalOptic (a ** c) (b ** c) a b
_1 = mkMonoidal @c (swap @k @a @c) (swap @k @c @b)

_2 :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => MonoidalOptic (c ** a) (c ** b) a b
_2 = mkMonoidal @c (obj2 @c @a) (obj2 @c @b)

instance (Cartesian k, Ob c) => Strong ProdAction (Rep (Constant c) :: k +-> k) where
  act @(PR x) (Rep @b @_ @a f) = withObProd @k @x @b (Rep (f . snd @k @x @a)) \\ f
instance Strong CoprodAction (Rep (Constant (P.First c)) :: Type +-> Type) where
  act (Rep f) = Rep (either (const (P.First Nothing)) f)

type Lens (s :: k) (t :: k) a b = Optic (Strong ProdAction) s t a b
mkLens
  :: forall {k} (s :: k) (t :: k) a b
   . (HasProducts k, Ob b) => (s ~> a) -> ((s && b) ~> t) -> Lens s t a b
mkLens sa sbt = ex2prof (ExOptic @(PR s) (id &&& sa) sbt) \\ sa

type VLLens s t a b = forall f. (P.Functor f) => (a -> f b) -> s -> f t
toVLLens :: Lens s t a b -> VLLens s t a b
toVLLens (Optic l) = (unPrelude .) . unStar . l . Star . (Prelude .)

fromVLLens :: VLLens s t a b -> Lens s t a b
fromVLLens f = mkLens (getConst . f Const) (P.uncurry (f (const id)))

type Prism (s :: k) t a b = Optic (Strong CoprodAction) s t a b
mkPrism :: forall {k} (s :: k) (t :: k) a b. (HasCoproducts k, Ob a) => (s ~> (t || a)) -> (b ~> t) -> Prism s t a b
mkPrism sta bt = ex2prof (ExOptic @(COPR t) sta (id ||| bt)) \\ bt

type Traversal s t a b = Optic Dist.StrongDistributiveProfunctor s t a b
traversing :: forall t a b. (Dist.Traversable t, Representable t, Ob a, Ob b) => Traversal (t % a) (t % b) a b
traversing = withObRep @t @a $ withObRep @t @b $ Optic (Dist.repTraverse @t)

type HaskTraversal s t a b = Optic (Dist.StrongDistributiveProfunctor :&&: Representable) s t a b
haskTraversing :: (P.Traversable t) => HaskTraversal (t a) (t b) a b
haskTraversing @t =
  Optic
    ( tabulate
        . (flip (index . unFromProfunctor) () .)
        . P.traverse @t
        . (\p a -> FromProfunctor (lmap (const a) p))
    )

class (Monad m) => Algebra m a where algebra :: m a -> a
instance (Monad m) => Algebra m (m a) where algebra = (>>= id)
instance (Monad m) => Algebra m () where algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where
  algebra mab = (algebra (fmap fst mab), algebra (fmap snd mab))

type AlgAction m = SubAction (Algebra m) Tensor
type AlgebraicLens m s t a b = Optic (Strong (AlgAction m)) s t a b
mkAlgebraicLens :: forall m s t a b. (Monad m) => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u = ex2prof (ExOptic (\s -> (return @m s, v s)) (uncurry u))

data Previewing a (b :: Type) s (t :: Type) where
  Previewing :: {unPreview :: s -> Maybe a} -> Previewing a b s t
instance Profunctor (Previewing a b) where
  dimap l _ (Previewing f) = Previewing (f . l)
  r \\ Previewing f = r \\ f
instance Strong CoprodAction (Previewing a b) where
  act (Previewing f) = Previewing (either (const Nothing) f)
instance Strong ProdAction (Previewing a b) where
  act (Previewing f) = Previewing (f . snd)

infixl 8 ?.
(?.)
  :: s -> (Previewing a b a b -> Previewing a b s t) -> Maybe a
(?.) s l = unPreview (l $ Previewing Just) s

type KlCat m = KLEISLI (Star (Prelude m))
data Updating a b s t where
  Update
    :: {unUpdate :: b -> s -> m t} -> Updating (KL a :: KlCat m) (KL b :: KlCat m) (KL s :: KlCat m) (KL t :: KlCat m)
instance (Monad m) => Profunctor (Updating a b :: KlCat m +-> KlCat m) where
  dimap (Kleisli (Star l)) (Kleisli (Star r)) (Update u) = Update (\b x -> do y <- unPrelude (l x); z <- u b y; unPrelude (r z))
  r \\ Update u = r \\ u
instance (Monad m) => Strong Tensor (Updating a b :: KlCat m +-> KlCat m) where
  act (Update u) = Update (\b (a, x) -> (a,) `fmap` u b x)

mupdate
  :: (Monad m)
  => (Updating (KL a :: KlCat m) (KL b :: KlCat m) (KL a) (KL b) -> Updating (KL a) (KL b) (KL s :: KlCat m) (KL t :: KlCat m))
  -> b
  -> s
  -> m t
mupdate f = unUpdate $ f (Update (\b _ -> return b))

newtype Replacing a b s t = Replace {unReplace :: (a -> b) -> (s -> t)}
instance Profunctor (Replacing a b) where
  dimap l r (Replace f) = Replace (\ab -> r . f ab . l)
instance Strong Tensor (Replacing a b) where
  act (Replace f) = Replace (\u -> map (f u))
instance Strong CoprodAction (Replacing a b) where
  act (Replace f) = Replace (\u -> map (f u))
instance Strong ApplyAction (Replacing a b) where
  act (Replace f) = Replace (\u -> map (f u))

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
instance (Monad m) => Strong (AlgAction m) (Classifying m a b) where
  act (Classifying f) = Classifying (\m b -> (algebra (fmap fst m), f (fmap snd m) b))

infixl 8 .?
(.?) :: (Monad m) => (Classifying m a b a b -> Classifying m a b s t) -> b -> m s -> t
(.?) l b ms = unClassify (l $ Classifying (const id)) ms b

instance (Strong act p) => Costrong act (Re p s t) where
  coact @a (Re f) = Re (f . act @act @_ @a)
instance (Costrong act p) => Strong act (Re p s t) where
  act @a @x @y (Re f) = withObRep @act @'(a, x) $ withObRep @act @'(a, y) $ Re (f . coact @act @_ @a)
instance InvertableOptic (Strong t) (Costrong t)
instance InvertableOptic (Costrong t) (Strong t)

v1Optic :: Traversal (G.V1 a) (G.V1 a') a a'
v1Optic = Optic \_ -> dimap (\case {}) (\case {}) nil

u1Optic :: Traversal (G.U1 a) (G.U1 a') a a'
u1Optic = Optic \_ -> dimap (const ()) (\() -> G.U1) one

par1Optic :: Traversal (G.Par1 a) (G.Par1 a') a a'
par1Optic = Optic (dimap G.unPar1 G.Par1)

rec1Optic :: Traversal (f a) (f a') a a' -> Traversal (G.Rec1 f a) (G.Rec1 f a') a a'
rec1Optic (Optic l) = Optic \p -> dimap G.unRec1 G.Rec1 (l p)

m1Optic :: Traversal (f a) (f a') a a' -> Traversal (G.M1 i k f a) (G.M1 i k f a') a a'
m1Optic (Optic l) = Optic \p -> dimap G.unM1 G.M1 (l p)

k1Optic :: forall i k a a'. Traversal (G.K1 i k a) (G.K1 i k a') a a'
k1Optic = Optic \_ -> dimap G.unK1 G.K1 strongId

plusOptic
  :: Traversal (p a) (p a') a a'
  -> Traversal (q a) (q a') a a'
  -> Traversal ((p G.:+: q) a) ((p G.:+: q) a') a a'
plusOptic (Optic l) (Optic r) = Optic \p -> dimap (\case G.L1 f -> Left f; G.R1 f -> Right f) (either G.L1 G.R1) (l p ++ r p)

multOptic
  :: Traversal (p a) (p a') a a'
  -> Traversal (q a) (q a') a a'
  -> Traversal ((p G.:*: q) a) ((p G.:*: q) a') a a'
multOptic (Optic l) (Optic r) = Optic \p -> dimap (\(f G.:*: g) -> (f, g)) (uncurry (G.:*:)) (l p ** r p)

compOptic
  :: Traversal (p (q a)) (p (q a')) (q a) (q a')
  -> Traversal (q a) (q a') a a'
  -> Traversal ((p G.:.: q) a) ((p G.:.: q) a') a a'
compOptic (Optic l) (Optic r) = Optic \p -> dimap G.unComp1 G.Comp1 (l (r p))