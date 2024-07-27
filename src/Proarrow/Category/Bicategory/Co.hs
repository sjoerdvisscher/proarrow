{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Co where

import Proarrow.Category.Bicategory
  ( Bicategory (..)
  , Comonad (..)
  , Fold
  , Monad (..)
  , Path (..)
  , SPath (..)
  , asObj
  , singPath
  , type (+++)
  )
import Proarrow.Category.Bicategory.Kan
  ( LeftKanExtension (..)
  , LeftKanLift (..)
  , RightKanExtension (..)
  , RightKanLift (..)
  )
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Object (obj)

type COK :: CAT k -> CAT k
newtype COK kk j k = CO (kk j k)
type instance UN CO (CO k) = k

type Co :: CAT (COK kk j k)
data Co a b where
  Co :: b ~> a -> Co (CO a) (CO b)

instance (CategoryOf (kk j k)) => Profunctor (Co :: CAT (COK kk j k)) where
  dimap = dimapDefault
  r \\ Co f = r \\ f
instance (CategoryOf (kk j k)) => Promonad (Co :: CAT (COK kk j k)) where
  id = Co id
  Co f . Co g = Co (g . f)
instance (CategoryOf (kk j k)) => CategoryOf (COK kk j k) where
  type (~>) = Co
  type Ob a = (Is CO a, Ob (UN CO a))

-- | Create a dual of a bicategory by reversing the 2-cells.
instance (Bicategory kk) => Bicategory (COK kk) where
  type Ob0 (COK kk) k = Ob0 kk k
  type I = CO I
  type a `O` b = CO (UN CO a `O` UN CO b)
  r \\\ Co f = r \\\ f
  Co f `o` Co g = Co (f `o` g)
  leftUnitor (Co p) = Co (leftUnitorInv p)
  leftUnitorInv (Co p) = Co (leftUnitor p)
  rightUnitor (Co p) = Co (rightUnitorInv p)
  rightUnitorInv (Co p) = Co (rightUnitor p)
  associator (Co p) (Co q) (Co r) = Co (associatorInv p q r)
  associatorInv (Co p) (Co q) (Co r) = Co (associator p q r)

concatFoldCo
  :: forall {kk} {i} {j} {k} {ps :: Path (COK kk) i j} (qs :: Path (COK kk) j k)
   . (Bicategory kk, Ob qs, Ob0 kk i, Ob0 kk j, Ob0 kk k)
  => SPath ps -> UN CO (Fold ps) `O` UN CO (Fold qs) ~> UN CO (Fold (ps +++ qs))
concatFoldCo SNil = leftUnitor (obj @(UN CO (Fold qs)))
concatFoldCo (SCons (Co p) SNil) = case singPath @qs of
  SNil -> rightUnitor p
  SCons{} -> p `o` obj @(UN CO (Fold qs))
concatFoldCo (SCons @_ @ps1 (Co p) ps@SCons{}) =
  (p `o` concatFoldCo @qs ps)
    . associator p (obj @(UN CO (Fold ps1))) (obj @(UN CO (Fold qs)))
    \\ asObj ps

splitFoldCo
  :: forall {kk} {i} {j} {k} {ps :: Path (COK kk) i j} (qs :: Path (COK kk) j k)
   . (Bicategory kk, Ob qs, Ob0 kk i, Ob0 kk j, Ob0 kk k)
  => SPath ps -> UN CO (Fold (ps +++ qs)) ~> UN CO (Fold ps) `O` UN CO (Fold qs)
splitFoldCo SNil = leftUnitorInv (obj @(UN CO (Fold qs)))
splitFoldCo (SCons (Co p) SNil) = case singPath @qs of
  SNil -> rightUnitorInv p
  SCons{} -> p `o` obj @(UN CO (Fold qs))
splitFoldCo (SCons @_ @ps1 (Co p) ps@SCons{}) =
  associatorInv p (obj @(UN CO (Fold ps1))) (obj @(UN CO (Fold qs)))
    . (p `o` splitFoldCo @qs ps)
    \\ asObj ps

instance (Comonad m) => Monad (CO m) where
  eta = Co epsilon
  mu = Co delta

instance (Monad m) => Comonad (CO m) where
  epsilon = Co eta
  delta = Co mu

instance (RightKanExtension j f) => LeftKanExtension (CO j) (CO f) where
  type Lan (CO j) (CO f) = CO (Ran j f)
  lan = Co (ran @j @f)
  lanUniv (Co n) = Co (ranUniv @j @f n)

instance (LeftKanExtension j f) => RightKanExtension (CO j) (CO f) where
  type Ran (CO j) (CO f) = CO (Lan j f)
  ran = Co (lan @j @f)
  ranUniv (Co n) = Co (lanUniv @j @f n)

instance (RightKanLift j f) => LeftKanLift (CO j) (CO f) where
  type Lift (CO j) (CO f) = CO (Rift j f)
  lift = Co (rift @j @f)
  liftUniv (Co n) = Co (riftUniv @j @f n)

instance (LeftKanLift j f) => RightKanLift (CO j) (CO f) where
  type Rift (CO j) (CO f) = CO (Lift j f)
  rift = Co (lift @j @f)
  riftUniv (Co n) = Co (liftUniv @j @f n)
