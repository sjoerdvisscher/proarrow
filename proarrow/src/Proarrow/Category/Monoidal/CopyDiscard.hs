{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Monoidal categories in which every object can be copied and discarded coherently:
-- 'CopyDiscard' supplies @'copy' :: a ~> a ** a@ and @'discard' :: a ~> 'Unit'@, giving the
-- projections 'fst'\/'snd' without requiring @tensor = product@ -- e.g. the biproduct categories
-- "Proarrow.Category.Instance.Mat" and "Proarrow.Category.Instance.FinRel". Concretely it is a
-- __cocommutative comonoid supply__: every object is a 'Proarrow.Monoid.CocommutativeComonoid'
-- (the @'Supplies' 'CocommutativeComonoid' k@ superclass) and @copy@\/@discard@ default to its
-- comult\/counit. Unlike 'Proarrow.Limit.BinaryProduct.Cartesian'
-- the comonoids need not be /natural/, so morphisms may duplicate\/delete resources non-uniformly.
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

class (SymMonoidal k, Supplies CocommutativeComonoid k) => CopyDiscard k where
  copy :: (Ob (a :: k)) => a ~> a ** a
  copy = comult
  discard :: (Ob (a :: k)) => a ~> Unit
  discard = counit

copyS :: (CopyDiscard k, Ob (a :: k)) => '[a] ~> '[a, a]
copyS = Str copy

discardS :: (CopyDiscard k, Ob (a :: k)) => '[a] ~> '[]
discardS = Str discard

instance (HasProducts k) => CopyDiscard (PROD k)
instance CopyDiscard Type
instance CopyDiscard ()

-- | The comonoid supply of a product category, a subcategory and a strictified category are
-- inherited componentwise: each object's comonoid is the ambient 'copy'\/'discard'.
instance (CopyDiscard j, CopyDiscard k, Ob (a :: (j, k))) => Comonoid (a :: (j, k)) where
  counit = discard
  comult = copy

instance (CopyDiscard j, CopyDiscard k, Ob (a :: (j, k))) => CocommutativeComonoid (a :: (j, k))

instance (CopyDiscard j, CopyDiscard k) => CopyDiscard (j, k) where
  copy = copy :**: copy
  discard = discard :**: discard

instance (SubMonoidal ob, CopyDiscard k, Ob (a :: SUBCAT ob)) => Comonoid (a :: SUBCAT (ob :: OB k)) where
  counit = discard
  comult = copy
instance (SubMonoidal ob, CopyDiscard k, Ob (a :: SUBCAT ob)) => CocommutativeComonoid (a :: SUBCAT (ob :: OB k))
instance (SubMonoidal ob, CopyDiscard k) => CopyDiscard (SUBCAT (ob :: OB k)) where
  copy = Sub copy
  discard = Sub discard

instance (CopyDiscard k, Ob (as :: [k])) => Comonoid (as :: [k]) where
  counit = discard
  comult = copy
instance (CopyDiscard k, Ob (as :: [k])) => CocommutativeComonoid (as :: [k])
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
