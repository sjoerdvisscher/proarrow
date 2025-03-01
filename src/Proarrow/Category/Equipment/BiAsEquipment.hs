module Proarrow.Category.Equipment.BiAsEquipment where

import Proarrow.Category.Bicategory (Bicategory (..), Ob0', leftUnitor', leftUnitorInv')
import Proarrow.Category.Bicategory.Bidiscrete (Bidiscrete (..), DiscreteK (..))
import Proarrow.Category.Equipment
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type data WKK kk i j = WK (kk i j)
type instance UN WK (WK p) = p

type W :: CAT (WKK kk i j)
data W a b where
  W :: a ~> b -> W (WK a) (WK b)
instance (CategoryOf (kk i j)) => Profunctor (W :: CAT (WKK kk i j)) where
  dimap = dimapDefault
  r \\ W p = r \\ p
instance (CategoryOf (kk i j)) => Promonad (W :: CAT (WKK kk i j)) where
  id = W id
  W f . W g = W (f . g)
instance (CategoryOf (kk i j)) => CategoryOf (WKK kk i j) where
  type (~>) = W
  type Ob (a :: WKK kk i j) = (Is WK a, Ob (UN WK a))

instance (Bicategory kk) => Bicategory (WKK kk) where
  type Ob0 (WKK kk) k = Ob0 kk k
  type I = WK I
  type O a b = WK (UN WK a `O` UN WK b)
  withOb2 @(WK a) @(WK b) = withOb2 @kk @a @b
  r \\\ W f = r \\\ f
  W f `o` W g = W (f `o` g)
  leftUnitor = W leftUnitor
  leftUnitorInv = W leftUnitorInv
  rightUnitor = W rightUnitor
  rightUnitorInv = W rightUnitorInv
  associator @(WK p) @(WK q) @(WK r) = W (associator @kk @p @q @r)
  associatorInv @(WK p) @(WK q) @(WK r) = W (associatorInv @kk @p @q @r)

-- | A bicategory as a proarrow equipment with only identity arrows vertically.
instance (Bicategory kk) => HasCompanions (WKK kk) (DiscreteK (Ob0' kk)) where
  type Companion (WKK kk) DK = WK I
  mapCompanion Bidiscrete = id
  compToId = W id
  compFromId = W id
  compToCompose Bidiscrete Bidiscrete = W (leftUnitorInv' id)
  compFromCompose Bidiscrete Bidiscrete = W (leftUnitor' id)

instance (Bicategory kk) => Equipment (WKK kk) (DiscreteK (Ob0' kk)) where
  type Conjoint (WKK kk) DK = WK I
  mapConjoint Bidiscrete = id
  conjToId = W id
  conjFromId = W id
  conjToCompose Bidiscrete Bidiscrete = W (leftUnitorInv' id)
  conjFromCompose Bidiscrete Bidiscrete = W (leftUnitor' id)
  comConUnit Bidiscrete = W (leftUnitorInv' id)
  comConCounit Bidiscrete = W (leftUnitor' id)