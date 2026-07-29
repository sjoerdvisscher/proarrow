module Proarrow.Category.Instance.PointedHask where

import Control.Monad ((>=>))
import Data.Kind (Type)
import Data.Map.Lazy qualified as Map
import Data.Map.Merge.Lazy qualified as Map
import Data.Maybe qualified as P
import Data.Void (Void, absurd)
import GHC.Generics (Generic)
import Prelude (Eq, Maybe (..), Ord, Show, const, ($), (>>=), type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Applicative (Applicative (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (FromProd (..), HasBinaryProducts (..), Prod (..))
import Proarrow.Object.Copower (Copowered (..))
import Proarrow.Object.Initial (HasInitialObject (..), HasZeroObject (..))
import Proarrow.Object.Power (Powered (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))

type data POINTED = P Type

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
  Pt f . Pt g = Pt (g >=> f)

-- | The category of types with an added point and point-preserving morphisms.
instance CategoryOf POINTED where
  type (~>) = Pointed
  type Ob a = (a ~ P (UN P a))

data These a b = This a | That b | These a b
  deriving (Eq, Show, Generic)
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
  one = Pt Just
  Pt f ** Pt g = Pt (\(a, b) -> liftA2 id (f a, g b))

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

-- This doesn't quite work, see tests.
-- We should have a -> Maybe b = Maybe (a ~~> b)
-- So a -> Maybe b as exponential is too big, it is not allowed to always return Nothing.
-- https://ncatlab.org/nlab/show/pointed+object#ClosedMonoidalStructure
-- instance Closed POINTED where
--   type P a ~~> P b = P (a -> Maybe b)
--   withObExp r = r
--   curry (Pt f) = Pt (\a -> Just (\b -> f (a, b)))
--   apply = Pt (\(f, b) -> f b)

instance Powered Type POINTED where
  type P a ^ n = P (n -> Maybe a)
  withObPower r = r
  power f = Pt (\a -> Just \n -> unPt (f n) a)
  unpower (Pt f) n = Pt (f >=> ($ n))

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
underlyingPt :: (HasZeroObject k) => (a :: k) ~> b -> Unit ~> P (a ~> b)
underlyingPt f = Pt \() -> Just f

enrichedPt :: (Ob (a :: k), Ob b, HasZeroObject k) => Unit ~> P (a ~> b) -> a ~> b
enrichedPt (Pt f) = P.fromMaybe zero (f ())

compPt :: (Ob (a :: k), Ob b, Ob c, HasZeroObject k) => P (b ~> c) ** P (a ~> b) ~> P (a ~> c)
compPt = Pt \(bc, ab) -> Just (bc . ab)

type FromPointed :: (Type -> Type) -> (POINTED -> Type)
data FromPointed f a where
  FromPointed :: {unFromPointed :: f a} -> FromPointed f (P a)

type Filterable f = Functor (FromPointed f)

mapMaybe :: (Filterable f) => (a -> Maybe b) -> f a -> f b
mapMaybe f = unFromPointed . map (Pt f) . FromPointed

instance Functor (FromPointed []) where
  map (Pt f) (FromPointed as) = FromPointed (P.mapMaybe f as)

instance Functor (FromPointed (Map.Map k)) where
  map (Pt f) (FromPointed m) = FromPointed (Map.mapMaybe f m)

-- | Not quite Align from the semialign package.
-- This requires being able to dynamically decide per position if it is included in the result.
-- So more like @merge@ from Data.Map.
type Align f = Applicative (FromProd (FromPointed f))

alignWith :: (Align f) => (These a b -> Maybe c) -> f a -> f b -> f c
alignWith f fa fb = unFromPointed $ unFromProd $ liftA2 (Prod (Pt f)) (FromProd (FromPointed fa), FromProd (FromPointed fb))

nil :: (Align f) => f a
nil = unFromPointed $ unFromProd $ pure (Prod (Pt (const Nothing))) ()

instance Applicative (FromProd (FromPointed [])) where
  pure a () = FromProd (FromPointed []) \\ a
  liftA2 (Prod (Pt f)) (FromProd (FromPointed fa), FromProd (FromPointed fb)) = FromProd (FromPointed (merge fa fb))
    where
      merge as [] = mapMaybe (f . This) as
      merge [] bs = mapMaybe (f . That) bs
      merge (a : as) (b : bs) = case f (These a b) of
        Nothing -> merge as bs
        Just c -> c : merge as bs

instance (Ord k) => Applicative (FromProd (FromPointed (Map.Map k))) where
  pure a () = FromProd (FromPointed Map.empty) \\ a
  liftA2 (Prod (Pt f)) (FromProd (FromPointed fa), FromProd (FromPointed fb)) = FromProd (FromPointed (merge fa fb))
    where
      merge =
        Map.merge
          (Map.mapMaybeMissing \_ a -> f (This a))
          (Map.mapMaybeMissing \_ b -> f (That b))
          (Map.zipWithMaybeMatched \_ a b -> f (These a b))
