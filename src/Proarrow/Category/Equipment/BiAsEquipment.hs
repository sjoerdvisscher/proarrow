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
  iObj = W iObj
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
  mapCompanion Bidiscrete = iObj
  compToId = W iObj
  compFromId = W iObj
  compToCompose Bidiscrete Bidiscrete = W (leftUnitorInv' iObj)
  compFromCompose Bidiscrete Bidiscrete = W (leftUnitor' iObj)

instance (Bicategory kk) => Equipment (WKK kk) (DiscreteK (Ob0' kk)) where
  type Conjoint (WKK kk) DK = WK I
  mapConjoint Bidiscrete = iObj
  conjToId = W iObj
  conjFromId = W iObj
  conjToCompose Bidiscrete Bidiscrete = W (leftUnitorInv' iObj)
  conjFromCompose Bidiscrete Bidiscrete = W (leftUnitor' iObj)
  comConUnit Bidiscrete = W (leftUnitorInv' iObj)
  comConCounit Bidiscrete = W (leftUnitor' iObj)