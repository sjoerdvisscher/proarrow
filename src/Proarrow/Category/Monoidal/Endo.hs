{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Monoidal.Endo where

import Data.Function (($))

import Proarrow.Core (Promonad(..), CategoryOf(..), Profunctor(..), Kind)
import Proarrow.Category.Bicategory (Path(..), Bicategory(..), MKKIND, type (+++), withAssociative)
import Proarrow.Category.Monoidal (MONOIDAL, Monoidal(..))
import Proarrow.Category.Instance.List (IsList (..), List (..), type (++))
import Proarrow.Object (obj)


type family ListToPath (ps :: [Path kk k k]) :: Path kk k k where
  ListToPath '[] = Nil
  ListToPath (p ': ps) = p +++ ListToPath ps

listToPath :: (Bicategory kk, Ob0 kk k) => List (as :: [Path kk k k]) bs -> ListToPath as ~> ListToPath bs
listToPath Nil = id
listToPath (Cons f fs) = f `o` listToPath fs

appendListToPath'
  :: forall {kk} {k} (as :: [Path kk k k]) bs r. (Bicategory kk, Ob0 kk k, Ob bs, Ob (ListToPath bs))
  => List as as -> ((ListToPath as +++ ListToPath bs ~ ListToPath (as ++ bs), Ob (as ++ bs)) => r) -> r
appendListToPath' Nil r = r
appendListToPath' (Cons @_ @a @as' f fs) r = withAssociative @a @(ListToPath as') @(ListToPath bs) (appendListToPath' @as' @bs fs r)
  \\ f \\ listToPath fs

appendListToPath
  :: forall {kk} {k} (as :: [Path kk k k]) bs r. (Bicategory kk, Ob0 kk k, Ob as, Ob bs)
  => ((ListToPath as +++ ListToPath bs ~ ListToPath (as ++ bs), Ob (as ++ bs)) => r) -> r
appendListToPath r = appendListToPath' @as @bs (listId @as) r \\ listToPath (obj @bs)


type Endo :: forall {kk :: MKKIND} {k :: Kind}. MONOIDAL (Path kk k k)
data Endo as bs where
  Endo :: (Ob as, Ob bs) => ListToPath as ~> ListToPath bs -> Endo as bs

instance (Bicategory kk, Ob0 kk k) => Profunctor (Endo :: MONOIDAL (Path kk k k)) where
  dimap l r (Endo f) = Endo (listToPath r . f . listToPath l) \\ l \\ r
  r \\ Endo f = r \\ f

instance (Bicategory kk, Ob0 kk k) => Promonad (Endo :: MONOIDAL (Path kk k k)) where
  id :: forall (a :: [Path kk k k]). Ob a => Endo a a
  id = Endo $ listToPath $ listId @a
  Endo f . Endo g = Endo (f . g)

instance (Bicategory kk, Ob0 kk k, CategoryOf (kk k k)) => Monoidal (Endo :: MONOIDAL (Path kk k k)) where
  Endo @as @bs l `par` Endo @cs @ds r = appendListToPath @as @cs $ appendListToPath @bs @ds $ Endo (l `o` r)
