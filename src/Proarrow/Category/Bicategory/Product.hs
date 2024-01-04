{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Product where

import Data.Function (($))

import Proarrow.Category.Bicategory (Bicategory(..), MKKIND, BICAT, Path(..), IsPath(..), SPath(..), type (+++))
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault)
import Data.Kind (Type)

type PRODK :: MKKIND -> MKKIND -> MKKIND
data PRODK jj kk j k where
  PROD :: jj (Fst ik) (Fst jl) -> kk (Snd ik) (Snd jl) -> PRODK jj kk ik jl

type family PRODFST (p :: PRODK jj kk j k) :: jj (Fst j) (Fst k) where PRODFST (PROD p q) = p
type family PRODSND (p :: PRODK jj kk j k) :: kk (Snd j) (Snd k) where PRODSND (PROD p q) = q
type family Fst (p :: Type) :: Type where Fst (a, b) = a
type family Snd (p :: Type) :: Type where Snd (a, b) = b

type family FstPath (ps :: Path (PRODK jj kk) ik jl) :: Path jj (Fst ik) (Fst jl)
type instance FstPath Nil = Nil
type instance FstPath (pq ::: ps) = PRODFST pq ::: FstPath ps

type family SndPath (ps :: Path (PRODK jj kk) ik jl) :: Path kk (Snd ik) (Snd jl)
type instance SndPath Nil = Nil
type instance SndPath (pq ::: ps) = PRODSND pq ::: SndPath ps

fstSndPathAppend' :: forall {i} {j} {jj} {kk} (as :: Path (PRODK jj kk) i j) bs r. (Ob bs)
  => SPath as -> ((FstPath as +++ FstPath bs ~ FstPath (as +++ bs), SndPath as +++ SndPath bs ~ SndPath (as +++ bs), IsPath (as +++ bs)) => r) -> r
fstSndPathAppend' SNil r = r
fstSndPathAppend' (SCons @_ @ps ps) r = fstSndPathAppend' @ps @bs ps r

fstSndPathAppend :: forall {i} {j} {jj} {kk} (as :: Path (PRODK jj kk) i j) bs r. (Ob as, Ob bs)
  => ((FstPath as +++ FstPath bs ~ FstPath (as +++ bs), SndPath as +++ SndPath bs ~ SndPath (as +++ bs), IsPath (as +++ bs)) => r) -> r
fstSndPathAppend = fstSndPathAppend' @as @bs (singPath @as)

type Prod :: BICAT (PRODK jj kk)
data Prod as bs where
  Prod :: (Ob as, Ob bs) => FstPath as ~> FstPath bs -> SndPath as ~> SndPath bs -> Prod as bs

instance (CategoryOf (Path jj (Fst ik) (Fst jl)), CategoryOf (Path kk (Snd ik) (Snd jl))) => Profunctor (Prod :: CAT (Path (PRODK jj kk) ik jl)) where
  dimap = dimapDefault
  r \\ Prod f g = r \\ f \\ g
instance (CategoryOf (Path jj (Fst ik) (Fst jl)), CategoryOf (Path kk (Snd ik) (Snd jl))) => Promonad (Prod :: CAT (Path (PRODK jj kk) ik jl)) where
  id = Prod id id
  Prod f1 g1 . Prod f2 g2 = Prod (f1 . f2) (g1 . g2)
instance (CategoryOf (Path jj (Fst ik) (Fst jl)), CategoryOf (Path kk (Snd ik) (Snd jl))) => CategoryOf (Path (PRODK jj kk) ik jl) where
  type (~>) = Prod
  type Ob (ps :: Path (PRODK jj kk) ik jl) = (IsPath ps, Ob (FstPath ps), Ob (SndPath ps))

-- | The product bicategory of bicategories `jj` and `kk`.
instance (Bicategory jj, Bicategory kk) => Bicategory (PRODK jj kk) where
  type Ob0 (PRODK jj kk) jk = (Ob0 jj (Fst jk), Ob0 kk (Snd jk))
  type Ob1 (PRODK jj kk) p = ()
  Prod @as @bs f g `o` Prod @cs @ds f' g' =
    fstSndPathAppend @as @cs $ fstSndPathAppend @bs @ds $
      let ff' = f `o` f'; gg' = g `o` g' in Prod ff' gg' \\\ ff' \\\ gg'
  r \\\ Prod f g = r \\\ f \\\ g