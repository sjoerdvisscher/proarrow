{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Cat where

import Data.Kind (Constraint)
import Data.Function (($))
import Data.Proxy (Proxy(..))

import Proarrow.Category.Bicategory (Path(..), type (+++), BICAT, Bicategory (..))
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault, UN)
import Proarrow.Functor (Functor(..))
import Proarrow.Object (tgt)


newtype FunK j k = FK (j -> k)
type instance UN FK (FK p) = p

type family ApplyAll (fs :: Path FunK i j) (a :: i) :: j
type instance ApplyAll Nil a = a
type instance ApplyAll (f ::: fs) a = ApplyAll fs (UN FK f a)

type ApplyAppend :: forall {i} {j} {k}. Path FunK i j -> Path FunK j k -> i -> Constraint
class (ApplyAll (fs +++ gs) a ~ ApplyAll gs (ApplyAll fs a)) => ApplyAppend fs gs a
instance (ApplyAll (fs +++ gs) a ~ ApplyAll gs (ApplyAll fs a)) => ApplyAppend fs gs a

type FList :: forall {j} {k}. Path FunK j k -> Constraint
class FList (fs :: Path FunK j k) where
  mapAll :: a ~> b -> ApplyAll fs a ~> ApplyAll fs b
  withAppendFList' :: FList gs => proxy gs -> ((FList (fs +++ gs), forall a. ApplyAppend fs gs a) => r) -> r
instance FList Nil where
  mapAll f = f
  withAppendFList' _ r = r
instance (Functor f, FList fs) => FList (FK f ::: fs) where
  mapAll f = mapAll @fs (map @f f)
  withAppendFList' = withAppendFList' @fs

withAppendFList :: forall fs gs r. (FList fs, FList gs) => ((FList (fs +++ gs), forall a. ApplyAppend fs gs a) => r) -> r
withAppendFList = withAppendFList' @fs (Proxy @gs)


type Cat :: BICAT FunK
data Cat fs gs where
  Cat
    :: forall {j} {k} (fs :: Path FunK j k) gs
     . (CategoryOf j, CategoryOf k, Ob fs, Ob gs)
    -- A definition of natural transformations that is easier to work with:
    => (forall a b. (a ~> b) -> ApplyAll fs a ~> ApplyAll gs b)
    -> Cat fs gs
instance (CategoryOf j, CategoryOf k) => Profunctor (Cat :: CAT (Path FunK j k)) where
  dimap = dimapDefault
  r \\ Cat{} = r
instance (CategoryOf j, CategoryOf k) => Promonad (Cat :: CAT (Path FunK j k)) where
  id :: forall (fs :: Path FunK j k). (Ob fs) => Cat fs fs
  id = Cat (mapAll @fs)
  Cat n . Cat m = Cat \f -> n (tgt f) . m f
instance (CategoryOf j, CategoryOf k) => CategoryOf (Path FunK j k) where
  type (~>) = Cat
  type Ob (fs :: Path FunK j k) = (CategoryOf j, CategoryOf k, FList fs)

-- | The bicategory Cat of categories, functors and natural transformations.
instance Bicategory FunK where
  type BiOb FunK k = CategoryOf k
  Cat @as @bs n `o` Cat @cs @ds m = withAppendFList @as @cs $ withAppendFList @bs @ds $ Cat $ m . n
  r \\\ Cat{} = r