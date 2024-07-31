{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Prof where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Adjunction qualified as A
import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..), Bimodule (..), Comonad (..), Monad (..))
import Proarrow.Category.Bicategory.Kan (RightKanExtension (..), RightKanLift (..))
import Proarrow.Category.Instance.Prof ()
import Proarrow.Category.Opposite (OPPOSITE (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Is
  , IsCategoryOf
  , PRO
  , Profunctor (..)
  , Promonad (..)
  , UN
  , arr
  , dimapDefault
  , lmap
  , rmap
  , (//)
  , (:~>)
  )
import Proarrow.Object (src, tgt)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Ran qualified as R
import Proarrow.Profunctor.Representable (Representable)
import Proarrow.Profunctor.Rift qualified as R
import Proarrow.Promonad (Procomonad (..))

type data ProfCl = ProfC | ProfRepC | ProfCorepC

type family ProfConstraint (cl :: ProfCl) :: PRO j k -> Constraint
type instance ProfConstraint ProfC = Profunctor
type instance ProfConstraint ProfRepC = Representable
type instance ProfConstraint ProfCorepC = Corepresentable

type data ProfK (cl :: ProfCl) j k = PK (PRO j k)
type instance UN PK (PK p) = p
type PROFK = ProfK ProfC

type Prof :: CAT (ProfK cl j k)
data Prof p q where
  Prof :: (Ob p, Ob q) => UN PK p :~> UN PK q -> Prof p q

instance Profunctor Prof where
  dimap = dimapDefault
  r \\ Prof n = r \\ n
instance Promonad Prof where
  id = Prof id
  Prof m . Prof n = Prof (m . n)
instance CategoryOf (ProfK cl j k) where
  type (~>) = Prof
  type
    Ob @(ProfK cl j k) p =
      (Is PK p, Profunctor (UN PK p), ProfConstraint cl (UN PK p))

class (ProfConstraint cl (p :.: q)) => ComposeConstraint cl i j k (p :: PRO i j) (q :: PRO j k)
instance (ProfConstraint cl (p :.: q)) => ComposeConstraint cl i j k (p :: PRO i j) (q :: PRO j k)

class (ProfConstraint cl (Id :: CAT k)) => IdConstraint cl k
instance (ProfConstraint cl (Id :: CAT k)) => IdConstraint cl k

instance
  ( forall i j k (p :: PRO i j) (q :: PRO j k). (ProfConstraint cl p, ProfConstraint cl q) => ComposeConstraint cl i j k p q
  , forall k. (CategoryOf k) => IdConstraint cl k
  )
  => Bicategory (ProfK cl)
  where
  type Ob0 (ProfK cl) k = CategoryOf k
  type I = PK Id
  type p `O` q = PK (UN PK p :.: UN PK q)
  Prof m `o` Prof n = Prof $ \(p :.: q) -> m p :.: n q
  r \\\ Prof{} = r
  leftUnitor (Prof n) = Prof $ \(Id h :.: q) -> n (lmap h q)
  leftUnitorInv (Prof n) = Prof $ \p -> Id (src p) :.: n p
  rightUnitor (Prof n) = Prof $ \(p :.: Id h) -> n (rmap h p)
  rightUnitorInv (Prof n) = Prof $ \p -> n p :.: Id (tgt p)
  associator Prof{} Prof{} Prof{} = Prof $ \((p :.: q) :.: r) -> p :.: (q :.: r)
  associatorInv Prof{} Prof{} Prof{} = Prof $ \(p :.: (q :.: r)) -> (p :.: q) :.: r

instance (Promonad p) => Monad (PK p :: PROFK k k) where
  eta = Prof (arr . getId)
  mu = Prof \(p :.: q) -> q . p

instance (Procomonad p) => Comonad (PK p :: PROFK k k) where
  epsilon = Prof (Id . extract)
  delta = Prof duplicate

instance
  (IsCategoryOf j cj, IsCategoryOf k ck, Profunctor p)
  => Bimodule (PK cj) (PK ck) (PK p :: PROFK j k)
  where
  leftAction = Prof \(f :.: p) -> lmap f p
  rightAction = Prof \(p :.: f) -> rmap f p

-- TODO; Fix order of arguments
instance (A.Adjunction r l) => Adjunction (PK l :: PROFK c d) (PK r) where
  unit = Prof \(Id f) -> lmap f A.unit \\ f
  counit = Prof (Id . A.counit)

instance (Profunctor f, Profunctor j) => RightKanExtension (PK j :: PROFK c d) (PK f :: PROFK c e) where
  type Ran (PK j) (PK f) = PK (R.Ran (OP j) f)
  ran = Prof \(j :.: r) -> R.runRan j r
  ranUniv (Prof n) = Prof \g -> g // R.Ran \j -> n (j :.: g)

instance (Profunctor f, Profunctor j) => RightKanLift (PK j :: PROFK d c) (PK f :: PROFK e c) where
  type Rift (PK j) (PK f) = PK (R.Rift (OP j) f)
  rift = Prof \(r :.: j) -> R.runRift j r
  riftUniv (Prof n) = Prof \g -> g // R.Rift \j -> n (g :.: j)
