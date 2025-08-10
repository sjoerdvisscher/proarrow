module Proarrow.Category.Instance.PointedHask where

import Data.Kind (Type)
import Prelude (Maybe (..), const, ($), (>>=), type (~))

import Data.Void (Void, absurd)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Applicative (liftA2)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Monoid (Comonoid (..), Monoid (..), CopyDiscard)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Copower (Copowered (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..), HasZeroObject (..))
import Proarrow.Object.Power (Powered (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))

type data POINTED = P Type
type instance UN P (P a) = a

type Pointed :: CAT POINTED
data Pointed a b where
  Pt :: {unPt :: a -> Maybe b} -> Pointed (P a) (P b)

toHask :: P a ~> P b -> (Maybe a -> Maybe b)
toHask (Pt f) = (>>= f)

instance Profunctor Pointed where
  dimap = dimapDefault
  r \\ Pt{} = r
instance Promonad Pointed where
  id = Pt Just
  Pt f . Pt g = Pt (\a -> g a >>= f)

-- | The category of types with an added point and point-preserving morphisms.
instance CategoryOf POINTED where
  type (~>) = Pointed
  type Ob a = (a ~ P (UN P a))

data These a b = This a | That b | These a b
instance HasBinaryProducts POINTED where
  type P a && P b = P (These a b)
  withObProd r = r
  fst = Pt (\case This a -> Just a; That _ -> Nothing; These a _ -> Just a)
  snd = Pt (\case This _ -> Nothing; That b -> Just b; These _ b -> Just b)
  Pt f &&& Pt g =
    Pt
      ( \a -> case (f a, g a) of
          (Just a', Just b') -> Just (These a' b')
          (Just a', Nothing) -> Just (This a')
          (Nothing, Just b') -> Just (That b')
          (Nothing, Nothing) -> Nothing
      )
instance HasTerminalObject POINTED where
  type TerminalObject = P Void
  terminate = Pt (const Nothing)

instance HasBinaryCoproducts POINTED where
  type P a || P b = P (a || b)
  withObCoprod r = r
  lft = Pt (Just . lft)
  rgt = Pt (Just . rgt)
  Pt f ||| Pt g = Pt (f ||| g)
instance HasInitialObject POINTED where
  type InitialObject = P Void
  initiate = Pt absurd

instance MonoidalProfunctor Pointed where
  par0 = Pt Just
  Pt f `par` Pt g = Pt (\(a, b) -> liftA2 id (f a, g b))

-- | The smash product of pointed sets.
-- Monoids relative to the smash product are absorption monoids.
instance Monoidal POINTED where
  type Unit = P ()
  type P a ** P b = P (a, b)
  withOb2 r = r
  leftUnitor = Pt (Just . snd)
  leftUnitorInv = Pt (Just . ((),))
  rightUnitor = Pt (Just . fst)
  rightUnitorInv = Pt (Just . (,()))
  associator = Pt (\((a, b), c) -> Just (a, (b, c)))
  associatorInv = Pt (\(a, (b, c)) -> Just ((a, b), c))

instance SymMonoidal POINTED where
  swap = Pt (Just . swap)
instance Closed POINTED where
  type P a ~~> P b = P (a -> Maybe b)
  withObExp r = r
  curry (Pt f) = Pt (\a -> Just (\b -> f (a, b)))
  apply = Pt (\(f, b) -> f b)

instance Powered Type POINTED where
  type P a ^ n = P (n -> Maybe a)
  withObPower r = r
  power f = Pt (\a -> Just \n -> unPt (f n) a)
  unpower (Pt f) n = Pt \a -> f a >>= ($ n)

instance Copowered Type POINTED where
  type n *. P a = P (n, a)
  withObCopower r = r
  copower f = Pt \(n, a) -> unPt (f n) a
  uncopower (Pt f) n = Pt \a -> f (n, a)

instance Monoid (P Void) where
  mempty = Pt (const Nothing)
  mappend = Pt (Just . fst)

-- | Lift Hask monoids.
memptyDefault :: (Monoid a) => Unit ~> P a
memptyDefault = Pt (Just . mempty)

mappendDefault :: (Monoid a) => P a ** P a ~> P a
mappendDefault = Pt (Just . mappend)

-- | Conjunction with False = Nothing, True = Just ()
instance Monoid (P ()) where
  mempty = memptyDefault
  mappend = mappendDefault

instance Monoid (P [a]) where
  mempty = memptyDefault
  mappend = mappendDefault

instance Comonoid (P x) where
  counit = Pt (Just . counit)
  comult = Pt (Just . comult)
instance CopyDiscard POINTED

-- | Categories with a zero object can be seen as categories enriched in Pointed.
underlyingPt :: HasZeroObject k => (a :: k) ~> b -> Unit ~> P (a ~> b)
underlyingPt f = Pt \() -> Just f

enrichedPt :: (Ob (a :: k), Ob b, HasZeroObject k) => Unit ~> P (a ~> b) -> a ~> b
enrichedPt (Pt f) = case f () of Just g -> g; Nothing -> zero

compPt :: (Ob (a :: k), Ob b, Ob c, HasZeroObject k) => P (b ~> c) ** P (a ~> b) ~> P (a ~> c)
compPt = Pt \(bc, ab) -> Just (bc . ab)