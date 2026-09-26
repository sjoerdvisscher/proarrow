{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-unused-foralls #-}

-- | Monoidal categories in which every object carries a cocommutative comonoid (the
-- @'Supplies' 'CocommutativeComonoid' k@ superclass), with @'copy' :: a ~> a ** a@ and
-- @'discard' :: a ~> 'Unit'@ defaulting to its comult\/counit. This gives projections
-- 'fst'\/'snd' without @tensor = product@, e.g. in the biproduct categories
-- "Proarrow.Category.Instance.Mat" and "Proarrow.Category.Instance.FinRel". Unlike in
-- 'Proarrow.Category.Monoidal.Cartesian.Cartesian' (which has this class as a superclass, by Fox's
-- theorem) the comonoids need not be /natural/, so morphisms may duplicate\/delete resources
-- non-uniformly.
module Proarrow.Category.Monoidal.CopyDiscard where

import Data.Kind (Constraint, Type)
import Prelude (Applicative, ($))

import Proarrow.Category.Instance.Bool (BOOL (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT, Sub (..), SubMonoidal)
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , Tensor
  , leftUnitorWith
  , rightUnitorWith
  , swapInner
  )
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..), listCase)
import Proarrow.Core (CategoryOf (..), Kind, OB, Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..), Supplies)
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Representable (Rep (..))
import Proarrow.Tools.Laws (Equation, Law (..), Laws (..), (===))

class (SymMonoidal k, Supplies CocommutativeComonoid k) => CopyDiscard k where
  copy :: (Ob (a :: k)) => a ~> a ** a
  copy = comult
  discard :: (Ob (a :: k)) => a ~> Unit
  discard = counit

-- | The constant functor ignores the acting object: discard it. Only copying\/discarding is
-- needed, so this works in biproduct categories as well as cartesian ones.
instance (CopyDiscard k, Ob r) => Strong Tensor (Rep (Constant r) :: k +-> k) where
  act @a (Rep @y p) = withOb2 @k @a @y (Rep (p . leftUnitorWith (discard @k @a))) \\ p

-- | The structures the laws of a copy-discard category are stated for.
type CopyDiscardStructures :: [Kind -> Constraint]
type CopyDiscardStructures = '[Monoidal, SymMonoidal, CopyDiscard]

-- | 'copy' and 'discard' are the supplied comonoid, and they respect the tensor: copying or
-- discarding @a '**' b@ is copying or discarding both parts, and on the unit they do nothing.
-- The comonoid laws and cocommutativity are those of the supply, in "Proarrow.Monoid".
instance Laws CopyDiscardStructures where
  laws =
    [ Law "copy is comult" \ @a _ -> copy @_ @a === comult @a
    , Law "discard is counit" \ @a _ -> discard @_ @a === counit @a
    , Law "copy of a tensor" \ @a @b _ ->
        withOb2 @_ @a @b $
          withOb2 @_ @a @a $
            withOb2 @_ @b @b $
              withOb2 @_ @(a ** b) @(a ** b) $
                copy @_ @(a ** b) === swapInner @a @a @b @b . (copy @_ @a ** copy @_ @b)
    , Law "discard of a tensor" \ @a @b _ ->
        withOb2 @_ @a @b (discard @_ @(a ** b) === leftUnitor @_ @Unit . (discard @_ @a ** discard @_ @b))
    , Law "copy of the unit" \ @a _ -> copyOfUnit @a
    , Law "discard of the unit" \ @a _ -> discardOfUnit @a
    ]

-- | 'copy' on the unit is a unitor; @a@ only says which category.
copyOfUnit :: forall {k} (a :: k) m. (CopyDiscard k, Applicative m) => m (Equation k)
copyOfUnit = withOb2 @k @Unit @Unit (copy @k @Unit === leftUnitorInv @k @Unit)

-- | 'discard' on the unit is the identity; @a@ only says which category.
discardOfUnit :: forall {k} (a :: k) m. (CopyDiscard k, Applicative m) => m (Equation k)
discardOfUnit = discard @k @Unit === obj @Unit

copyS :: (CopyDiscard k, Ob (a :: k)) => '[a] ~> '[a, a]
copyS = Str copy

discardS :: (CopyDiscard k, Ob (a :: k)) => '[a] ~> '[]
discardS = Str discard

instance CopyDiscard Type
instance CopyDiscard ()

instance CopyDiscard BOOL

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
