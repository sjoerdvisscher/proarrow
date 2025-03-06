module Proarrow.Category.Instance.PointedHask where

import Data.Kind (Type)
import Prelude (Maybe (..), type (~), const, maybe, (>>=), (++))

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Data.Void (Void, absurd)
import Proarrow.Category.Monoidal (Monoidal(..), MonoidalProfunctor (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Functor (map)
import Proarrow.Category.Monoidal.Applicative (liftA2)
import Proarrow.Monoid (Monoid (..), Comonoid (..))

type data POINTED = P Type
type instance UN P (P a) = a

type Pointed :: CAT POINTED
data Pointed a b where
  P :: (Maybe a -> Maybe b) -> Pointed (P a) (P b)

instance Profunctor Pointed where
  dimap = dimapDefault
  r \\ P{} = r
instance Promonad Pointed where
  id = P id
  P f . P g = P (f . g)
instance CategoryOf POINTED where
  type (~>) = Pointed
  type Ob a = (a ~ P (UN P a))

data These a b = This a | That b | These a b
instance HasBinaryProducts POINTED where
  type P a && P b = P (These a b)
  withObProd r = r
  fst = P (\case Nothing -> Nothing; Just (This a) -> Just a; Just (That _) -> Nothing; Just (These a _) -> Just a)
  snd = P (\case Nothing -> Nothing; Just (This _) -> Nothing; Just (That b) -> Just b; Just (These _ b) -> Just b)
  P f &&& P g = P (\a -> case (f a, g a) of
    (Just a', Just b') -> Just (These a' b')
    (Just a', Nothing) -> Just (This a')
    (Nothing, Just b') -> Just (That b')
    (Nothing, Nothing) -> Nothing)
instance HasTerminalObject POINTED where
  type TerminalObject = P Void
  terminate = P (const Nothing)

instance HasBinaryCoproducts POINTED where
  type P a || P b = P (a || b)
  withObCoprod r = r
  lft = P (map lft)
  rgt = P (map rgt)
  P f ||| P g = P (>>= (f . Just ||| g . Just))
instance HasInitialObject POINTED where
  type InitialObject = P Void
  initiate = P (maybe Nothing absurd)

instance MonoidalProfunctor Pointed where
  par0 = P id
  P f `par` P g = P (\case Nothing -> liftA2 id (f Nothing, g Nothing); Just (a, b) -> liftA2 id (f (Just a), g (Just b)))
-- | The smash product of pointed sets.
-- Monoids relative to the smash product are absorption monoids.
instance Monoidal POINTED where
  type Unit = P ()
  type P a ** P b = P (a, b)
  withOb2 r = r
  leftUnitor = P (map snd)
  leftUnitorInv = P (map ((),))
  rightUnitor = P (map fst)
  rightUnitorInv = P (map (,()))
  associator = P (\case
    Nothing -> Nothing
    Just ((a, b), c) -> Just (a, (b, c)))
  associatorInv = P (\case
    Nothing -> Nothing
    Just (a, (b, c)) -> Just ((a, b), c))

-- TODO Pointed is closed: https://ncatlab.org/nlab/show/pointed+object#ClosedMonoidalStructure

-- | Conjunction with False = Nothing, True = Just ()
instance Monoid (P ()) where
  mempty = P (const (Just ()))
  mappend = P (map fst)

instance Monoid (P Void) where
  mempty = P (const Nothing)
  mappend = P (map fst)

instance Monoid (P [a]) where
  mempty = P (map (const []))
  mappend = P (map (\(a, b) -> a ++ b))

instance Comonoid (P x) where
  counit = P (map (const ()))
  comult = P (map (\x -> (x, x)))