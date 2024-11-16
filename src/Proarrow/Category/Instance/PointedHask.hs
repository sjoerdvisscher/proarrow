module Proarrow.Category.Instance.PointedHask where

import Data.Kind (Type)
import Prelude (Maybe (..), type (~), const, maybe, (>>=))

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Object.BinaryProduct (HasBinaryProducts(..))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Data.Void (Void, absurd)
import Proarrow.Category.Monoidal (Monoidal(..), MonoidalProfunctor (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Functor (map)
import Proarrow.Category.Monoidal.Applicative (liftA2)

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
  lft = P (map lft)
  rgt = P (map rgt)
  P f ||| P g = P (>>= (f . Just ||| g . Just))
instance HasInitialObject POINTED where
  type InitialObject = P Void
  initiate = P (maybe Nothing absurd)

instance MonoidalProfunctor Pointed where
  par0 = P id
  P f `par` P g = P (\case Nothing -> liftA2 id (f Nothing, g Nothing); Just (a, b) -> liftA2 id (f (Just a), g (Just b)))
instance Monoidal POINTED where
  type Unit = P ()
  type P a ** P b = P (a, b)
  leftUnitor (P f) = P (f . map snd)
  leftUnitorInv (P f) = P (map ((),) . f)
  rightUnitor (P f) = P (f . map fst)
  rightUnitorInv (P f) = P (map (,()) . f)
  associator P{} P{} P{} = P (\case
    Nothing -> Nothing
    Just ((a, b), c) -> Just (a, (b, c)))
  associatorInv P{} P{} P{} = P (\case
    Nothing -> Nothing
    Just (a, (b, c)) -> Just ((a, b), c))