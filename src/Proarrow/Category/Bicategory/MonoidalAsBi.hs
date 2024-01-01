{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.MonoidalAsBi where

import Data.Function (($))

import Proarrow.Core (Promonad(..), CategoryOf(..), Profunctor(..), Is, UN, dimapDefault)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Instance.List (IsList, type (++))
import Proarrow.Category.Bicategory (MKKIND, Path(..), type (+++), BICAT, Bicategory (..), IsPath(..), SPath(..))


type MonK :: M.MONOIDAL k -> MKKIND
newtype MonK (m :: M.MONOIDAL k) i j = MK k

type family PathToList (p :: Path (MonK (m :: M.MONOIDAL k)) i j) :: [k]
type instance PathToList Nil = '[]
type instance PathToList (MK k ::: p) = k ': PathToList p

appendPathToList'
  :: forall {i} {j} {k} {m :: M.MONOIDAL k} (as :: Path (MonK m) i j) bs r. (Ob bs, CategoryOf k)
  => SPath as -> ((PathToList as ++ PathToList bs ~ PathToList (as +++ bs), Ob (as +++ bs)) => r) -> r
appendPathToList' SNil r = r
appendPathToList' (SCons @(MK p) @ps' ps) r = appendPathToList' @ps' @bs ps r

appendPathToList
  :: forall {i} {j} {k} {m :: M.MONOIDAL k} (as :: Path (MonK m) i j) bs r. (Ob as, Ob bs, CategoryOf k)
  => ((PathToList as ++ PathToList bs ~ PathToList (as +++ bs), Ob (as +++ bs)) => r) -> r
appendPathToList = appendPathToList' @as @bs (singPath @as)


instance (M.Monoidal m) => Profunctor (Mon2 :: BICAT (MonK m)) where
  dimap = dimapDefault
  r \\ Mon2 f = r \\ f
instance (M.Monoidal m) => Promonad (Mon2 :: BICAT (MonK (m :: M.MONOIDAL k))) where
  id = Mon2 id
  Mon2 f . Mon2 g = Mon2 (f . g)
instance (M.Monoidal m) => CategoryOf (Path (MonK (m :: M.MONOIDAL k)) i j) where
  type (~>) @(Path (MonK m) i j) = Mon2
  type Ob ps = (IsPath ps, IsList (PathToList ps))

type Mon2 :: BICAT (MonK m)
data Mon2 as bs where
  Mon2
    :: forall {i} {j} {k} m as bs. (Ob as, Ob bs)
    => m (PathToList as) (PathToList bs) -> Mon2 (as :: Path (MonK (m :: M.MONOIDAL k)) i j) bs

-- | A monoidal category as a one object bicategory.
instance M.Monoidal m => Bicategory (MonK (m :: M.MONOIDAL k)) where
  type Ob0 (MonK (m :: M.MONOIDAL k)) j = ()
  type Ob1 (MonK (m :: M.MONOIDAL k)) p = (Is MK p, Ob (UN MK p))
  Mon2 @_ @as @bs f `o` Mon2 @_ @cs @ds g = appendPathToList @as @cs $ appendPathToList @bs @ds $ Mon2 (f `M.par` g)
  r \\\ Mon2{} = r
  -- fromList Nil = Mon2 id
  -- fromList (Cons @p @q n ns) = case fromList ns of Mon2 m -> Mon2 (M.lift @m @p @q n `M.par` m)
