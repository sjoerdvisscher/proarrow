{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Monoidal categories in which every object can be copied and discarded coherently:
-- 'CopyDiscard' supplies @'copy' :: a ~> a ** a@ and @'discard' :: a ~> 'Unit'@, giving the
-- projections 'fst'\/'snd' without requiring @tensor = product@ -- e.g. the biproduct categories
-- "Proarrow.Category.Instance.Mat" and "Proarrow.Category.Instance.FinRel". Concretely it is a
-- __cocommutative comonoid supply__: @copy@\/@discard@ default to the
-- @'Proarrow.Monoid.CocommutativeComonoid'@ comult\/counit of each object (and every instance's
-- @copy@\/@discard@ are required to be one). Unlike 'Proarrow.Limit.BinaryProduct.Cartesian' they
-- need not be /natural/, so morphisms may duplicate\/delete resources non-uniformly.
module Proarrow.Category.Monoidal.CopyDiscard where

import Data.Kind (Type)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT, Sub (..), SubMonoidal)
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , leftUnitorWith
  , rightUnitorWith
  )
import Proarrow.Category.Monoidal.Strictified (Strictified (..), listCase)
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), obj)
import Proarrow.Limit.BinaryProduct (HasProducts, PROD (..))
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..), Supplies)

class (SymMonoidal k) => CopyDiscard k where
  copy :: (Ob (a :: k)) => a ~> a ** a
  default copy :: (Supplies CocommutativeComonoid k) => (Ob (a :: k)) => a ~> a ** a
  copy = comult
  discard :: (Ob (a :: k)) => a ~> Unit
  default discard :: (Supplies CocommutativeComonoid k) => (Ob (a :: k)) => a ~> Unit
  discard = counit

copyS :: (CopyDiscard k, Ob (a :: k)) => '[a] ~> '[a, a]
copyS = Str copy

discardS :: (CopyDiscard k, Ob (a :: k)) => '[a] ~> '[]
discardS = Str discard

instance (HasProducts k) => CopyDiscard (PROD k)
instance CopyDiscard Type
instance CopyDiscard ()
instance (CopyDiscard j, CopyDiscard k) => CopyDiscard (j, k) where
  copy = copy :**: copy
  discard = discard :**: discard

instance (SubMonoidal ob, CopyDiscard k) => CopyDiscard (SUBCAT (ob :: OB k)) where
  copy = Sub copy
  discard = Sub discard

instance (CopyDiscard k) => CopyDiscard [k] where
  copy @as0 =
    listCase @as0
      id
      (\ @a -> Str @'[a] @'[a, a] copy)
      ( \ @a @as ->
          (obj @'[a] ** (associator @_ @as @'[a] @as . (swap @[k] @'[a] @as ** obj @as)))
            . (Str @'[a] @'[a, a] copy ** copy)
      )
  discard @as =
    listCase @as
      id
      (Str discard)
      (\ @a -> Str @'[a] @'[] discard ** discard)

fst :: forall {k} (a :: k) b. (CopyDiscard k, Ob a, Ob b) => (a ** b) ~> a
fst = rightUnitorWith (discard @k @b)

snd :: forall {k} a (b :: k). (CopyDiscard k, Ob a, Ob b) => (a ** b) ~> b
snd = leftUnitorWith (discard @k @a)

(&&&) :: forall {k} (a :: k) x y. (CopyDiscard k) => a ~> x -> a ~> y -> a ~> x ** y
f &&& g = (f ** g) . copy \\ f
