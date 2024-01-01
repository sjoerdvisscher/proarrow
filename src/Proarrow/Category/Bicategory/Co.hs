{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Co where

import Data.Function (($))

import Proarrow.Category.Bicategory (Bicategory(..), MKKIND, BICAT, Path(..), IsPath(..), SPath(..), type (+++), isPathAppend)
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault, UN, Is)


type COK :: MKKIND -> MKKIND
newtype COK kk j k = CO (kk j k)
type instance UN CO (CO k) = k


type family UnCoPath (ps :: Path (COK kk) a b) :: Path kk a b
type instance UnCoPath Nil = Nil
type instance UnCoPath (CO p ::: ps) = p ::: UnCoPath ps

unCoPathAppend'
  :: forall {i} {j} {kk} (as :: Path (COK kk) i j) bs r. (Ob bs)
  => SPath as -> ((UnCoPath as +++ UnCoPath bs ~ UnCoPath (as +++ bs)) => r) -> r
unCoPathAppend' SNil r = r
unCoPathAppend' (SCons @(CO p) @ps' ps) r = unCoPathAppend' @ps' @bs ps r

unCoPathAppend
  :: forall {i} {j} {kk} (as :: Path (COK kk) i j) bs r. (Ob as, Ob bs)
  => ((UnCoPath as +++ UnCoPath bs ~ UnCoPath (as +++ bs)) => r) -> r
unCoPathAppend = unCoPathAppend' @as @bs (singPath @as)


type Co :: BICAT (COK kk)
data Co as bs where
  Co :: (Ob as, Ob bs) => UnCoPath bs ~> UnCoPath as -> Co as bs

instance (CategoryOf (Path kk j k)) => Profunctor (Co :: CAT (Path (COK kk) j k)) where
  dimap = dimapDefault
  r \\ Co f = r \\ f
instance (CategoryOf (Path kk j k)) => Promonad (Co :: CAT (Path (COK kk) j k)) where
  id = Co id
  Co f . Co g = Co (g . f)
instance (CategoryOf (Path kk j k)) => CategoryOf (Path (COK kk) j k) where
  type (~>) = Co
  type Ob (ps :: Path (COK kk) j k) = (IsPath ps, Ob (UnCoPath ps))

instance Bicategory kk => Bicategory (COK kk) where
  type Ob0 (COK kk) k = Ob0 kk k
  type Ob1 (COK kk) p = (Is CO p, Ob1 kk (UN CO p))
  Co @as @bs f `o` Co @cs @ds g =
    unCoPathAppend @as @cs $ unCoPathAppend @bs @ds $
    isPathAppend @as @cs $ isPathAppend @bs @ds $
    let fg = f `o` g in Co fg \\\ fg
  r \\\ Co f = r \\\ f