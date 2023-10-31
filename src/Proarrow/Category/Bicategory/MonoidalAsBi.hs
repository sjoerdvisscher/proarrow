{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.MonoidalAsBi where

import Data.Kind (Constraint)
import Data.Function (($))
import Data.Proxy (Proxy(..))

import Proarrow.Core (Promonad(..), CategoryOf(..), Profunctor(..), dimapDefault)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Instance.List (IsList, type (++))
import Proarrow.Category.Bicategory (MKKIND, Path(..), type (+++), BICAT, Bicategory (..))


type MonK :: M.MONOIDAL k -> MKKIND
newtype MonK (m :: M.MONOIDAL k) i j = MK k

type family PathToList (p :: Path (MonK (m :: M.MONOIDAL k)) i j) :: [k]
type instance PathToList Nil = '[]
type instance PathToList (MK k ::: p) = k ': PathToList p

type AppendPathToList :: forall {m} {i} {j}. Path (MonK m) i j -> Constraint
class AppendPathToList (as :: Path (MonK m) i j) where
  appendPathToList' :: AppendPathToList bs => proxy bs -> ((PathToList as ++ PathToList bs ~ PathToList (as +++ bs), AppendPathToList (as +++ bs)) => r) -> r
instance AppendPathToList Nil where
  appendPathToList' _ r = r
instance AppendPathToList as => AppendPathToList (MK k ::: as) where
  appendPathToList' = appendPathToList' @as

appendPathToList
  :: forall as bs r. (AppendPathToList as, AppendPathToList bs)
  => ((PathToList as ++ PathToList bs ~ PathToList (as +++ bs), AppendPathToList (as +++ bs)) => r) -> r
appendPathToList = appendPathToList' @as (Proxy @bs)

instance (M.Monoidal m) => Profunctor (Mon2 :: BICAT (MonK m)) where
  dimap = dimapDefault
  r \\ Mon2 f = r \\ f
instance (M.Monoidal m) => Promonad (Mon2 :: BICAT (MonK (m :: M.MONOIDAL k))) where
  id = Mon2 id
  Mon2 f . Mon2 g = Mon2 (f . g)
instance (M.Monoidal m) => CategoryOf (Path (MonK (m :: M.MONOIDAL k)) i j) where
  type (~>) @(Path (MonK m) i j) = Mon2
  type Ob ps = (IsList (PathToList ps), AppendPathToList ps)

type Mon2 :: BICAT (MonK m)
data Mon2 as bs where
  Mon2
    :: forall {i} {j} {k} m as bs. (AppendPathToList as, AppendPathToList bs)
    => m (PathToList as) (PathToList bs) -> Mon2 (as :: Path (MonK (m :: M.MONOIDAL k)) i j) bs

-- | A monoidal category as a one object bicategory.
instance M.Monoidal m => Bicategory (MonK (m :: M.MONOIDAL k)) where
  type BiOb (MonK (m :: M.MONOIDAL k)) j = ()
  Mon2 @_ @as @bs f `o` Mon2 @_ @cs @ds g = appendPathToList @as @cs $ appendPathToList @bs @ds $ Mon2 (f `M.par` g)
  r \\\ _ = r