{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Bicategory.Cat where

import Data.Kind (Constraint)
import Data.Function (($))

import Proarrow.Category.Bicategory (Path(..), type (+++), BICAT, Bicategory (..), IsPath(..), SPath(..))
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault)
import Proarrow.Functor (Functor(..))
import Proarrow.Object (tgt)


type family ApplyAll (fs :: Path (->) i j) (a :: i) :: j
type instance ApplyAll Nil a = a
type instance ApplyAll (f ::: fs) a = ApplyAll fs (f a)

type ApplyAppend :: forall {i} {j} {k}. Path (->) i j -> Path (->) j k -> i -> Constraint
class (ApplyAll (fs +++ gs) a ~ ApplyAll gs (ApplyAll fs a)) => ApplyAppend fs gs a
instance (ApplyAll (fs +++ gs) a ~ ApplyAll gs (ApplyAll fs a)) => ApplyAppend fs gs a

withAppendFList' :: forall fs gs r. (IsPath gs) => SPath fs -> ((IsPath (fs +++ gs), forall a. ApplyAppend fs gs a) => r) -> r
withAppendFList' SNil r = r
withAppendFList' (SCons @_ @fs' fs) r = withAppendFList' @fs' @gs fs r

withAppendFList :: forall fs gs r. (IsPath fs, IsPath gs) => ((IsPath (fs +++ gs), forall a. ApplyAppend fs gs a) => r) -> r
withAppendFList = withAppendFList' @fs @gs (singPath @fs)

mapAll :: SPath fs -> a ~> b -> ApplyAll fs a ~> ApplyAll fs b
mapAll SNil f = f
mapAll (SCons @f fs) f = mapAll fs (map @f f)


type Cat :: BICAT (->)
data Cat fs gs where
  Cat
    :: forall {j} {k} (fs :: Path (->) j k) gs
     . (CategoryOf j, CategoryOf k, Ob fs, Ob gs)
    -- A definition of natural transformations that is easier to work with:
    => (forall a b. (a ~> b) -> ApplyAll fs a ~> ApplyAll gs b)
    -> Cat fs gs
instance (CategoryOf j, CategoryOf k) => Profunctor (Cat :: CAT (Path (->) j k)) where
  dimap = dimapDefault
  r \\ Cat{} = r
instance (CategoryOf j, CategoryOf k) => Promonad (Cat :: CAT (Path (->) j k)) where
  id :: forall (fs :: Path (->) j k). (Ob fs) => Cat fs fs
  id = Cat (mapAll (singPath @fs))
  Cat n . Cat m = Cat \f -> n (tgt f) . m f
instance (CategoryOf j, CategoryOf k) => CategoryOf (Path (->) j k) where
  type (~>) = Cat
  type Ob (fs :: Path (->) j k) = IsPath fs

-- | The bicategory Cat of categories, functors and natural transformations.
instance Bicategory (->) where
  type Ob0 (->) k = CategoryOf k
  type Ob1 (->) f = Functor f
  Cat @as @bs n `o` Cat @cs @ds m = withAppendFList @as @cs $ withAppendFList @bs @ds $ Cat $ m . n
  r \\\ Cat{} = r