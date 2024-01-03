{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Op where

import Data.Function (($))

import Proarrow.Category.Bicategory (Bicategory(..), MKKIND, BICAT, Path(..), IsPath(..), SPath(..), type (+++), isPathAppend)
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault, UN, Is)


type OPK :: MKKIND -> MKKIND
newtype OPK kk j k = OP (kk k j)
type instance UN OP (OP k) = k

type UnOpPath ps = UnOpPath' ps Nil
type family UnOpPath' (ps :: Path (OPK kk) a b) (acc :: Path kk a c) :: Path kk b c
type instance UnOpPath' Nil acc = acc
type instance UnOpPath' (OP p ::: ps) acc = UnOpPath' ps (p ::: acc)

unOpPathNested
  :: forall {j} {k} {kk} as (bs :: Path (OPK kk) j k) cs r. ()
  => SPath bs -> (UnOpPath' bs (as +++ cs) ~ UnOpPath' bs as +++ cs => r) -> r
unOpPathNested SNil r = r
unOpPathNested (SCons @(OP p) @ps ps) r = unOpPathNested @(p ::: as) @ps @cs ps r

unOpPathAppend'
  :: forall {i} {j} {k} {kk} (as :: Path (OPK kk) i j) (bs :: Path (OPK kk) j k) cs r. (Ob bs)
  => SPath as -> (UnOpPath' bs (UnOpPath' as cs) ~ UnOpPath' (as +++ bs) cs => r) -> r
unOpPathAppend' SNil r = r
unOpPathAppend' (SCons @(OP p) @ps ps) r = unOpPathAppend' @ps @bs @(p ::: cs) ps r

unOpPathAppend
  :: forall {i} {j} {kk} (as :: Path (OPK kk) i j) bs r. (Ob as, Ob bs)
  => (UnOpPath bs +++ UnOpPath as ~ UnOpPath (as +++ bs) => r) -> r
unOpPathAppend r = unOpPathNested @Nil @bs @(UnOpPath as) (singPath @bs) $ unOpPathAppend' @as @bs @Nil (singPath @as) r


type Op :: BICAT (OPK kk)
data Op as bs where
  Op :: (Ob as, Ob bs) => UnOpPath as ~> UnOpPath bs -> Op as bs

instance (CategoryOf (Path kk j k)) => Profunctor (Op :: CAT (Path (OPK kk) k j)) where
  dimap = dimapDefault
  r \\ Op f = r \\ f
instance (CategoryOf (Path kk j k)) => Promonad (Op :: CAT (Path (OPK kk) k j)) where
  id = Op id
  Op f . Op g = Op (f . g)
instance (CategoryOf (Path kk j k)) => CategoryOf (Path (OPK kk) k j) where
  type (~>) = Op
  type Ob (ps :: Path (OPK kk) k j) = (IsPath ps, Ob (UnOpPath ps))

-- | Create a dual of a bicategory by reversing the 1-cells.
instance Bicategory kk => Bicategory (OPK kk) where
  type Ob0 (OPK kk) k = Ob0 kk k
  type Ob1 (OPK kk) p = (Is OP p, Ob1 kk (UN OP p))
  Op @as @bs f `o` Op @cs @ds g =
    unOpPathAppend @as @cs $ unOpPathAppend @bs @ds $
    isPathAppend @as @cs $ isPathAppend @bs @ds $
    let fg = g `o` f in Op fg \\\ fg
  r \\\ Op f = r \\\ f