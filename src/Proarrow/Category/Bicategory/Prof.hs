{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Prof where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Bicategory (Bicategory(..), Monad(..), Bimodule(..), Adjunction(..))
import Proarrow.Category.Bicategory.Kan (RightKanExtension(..), RightKanLift (..))
import Proarrow.Core (PRO, CategoryOf(..), Profunctor(..), (:~>), CAT, Promonad (..), dimapDefault, lmap, rmap, UN, Is, arr, IsCategoryOf, (//))
import Proarrow.Profunctor.Representable (Representable)
import Proarrow.Profunctor.Corepresentable (Corepresentable)
import Proarrow.Category.Instance.Prof ()
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Object (src, tgt)
import Proarrow.Adjunction qualified as A
import Proarrow.Profunctor.Ran qualified as R
import Proarrow.Profunctor.Rift qualified as R
import Proarrow.Category.Opposite (OPPOSITE(..))


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
  type Ob @(ProfK cl j k) p = (Is PK p, Profunctor (UN PK p), ProfConstraint cl (UN PK p), ProfConstraint cl ((~>) @j), ProfConstraint cl ((~>) @k))

class ProfConstraint cl (p :.: q) => ComposeConstraint cl i j k (p :: PRO i j) (q :: PRO j k)
instance ProfConstraint cl (p :.: q) => ComposeConstraint cl i j k (p :: PRO i j) (q :: PRO j k)

instance (forall i j k (p :: PRO i j) (q :: PRO j k). (ProfConstraint cl p, ProfConstraint cl q) => ComposeConstraint cl i j k p q) => Bicategory (ProfK cl) where
  type Ob0 (ProfK cl) k = (CategoryOf k, ProfConstraint cl ((~>) :: CAT k))
  type I = PK (~>)
  type p `O` q = PK (UN PK p :.: UN PK q)
  Prof m `o` Prof n = Prof $ \(p :.: q) -> m p :.: n q
  r \\\ Prof{} = r
  leftUnitor Prof{} = Prof $ \(h :.: q) -> lmap h q
  leftUnitorInv Prof{} = Prof $ \p -> src p :.: p
  rightUnitor Prof{} = Prof $ \(p :.: h) -> rmap h p
  rightUnitorInv Prof{} = Prof $ \p -> p :.: tgt p
  associator Prof{} Prof{} Prof{} = Prof $ \((p :.: q) :.: r) -> p :.: (q :.: r)
  associatorInv Prof{} Prof{} Prof{} = Prof $ \(p :.: (q :.: r)) -> (p :.: q) :.: r

instance Promonad p => Monad (PK p :: PROFK k k) where
  eta = Prof arr
  mu = Prof \(p :.: q) -> q . p

instance (IsCategoryOf j cj, IsCategoryOf k ck, Profunctor p) =>
    Bimodule (PK cj) (PK ck) (PK p :: PROFK j k) where
  leftAction = Prof \(f :.: p) -> lmap f p
  rightAction = Prof \(p :.: f) -> rmap f p

instance (A.Adjunction l r) => Adjunction (PK l :: PROFK c d) (PK r) where
  unit = Prof \f -> lmap f A.unit \\ f
  counit = Prof A.counit

instance (Profunctor f, Profunctor j) => RightKanExtension (PK j :: PROFK c d) (PK f :: PROFK c e) where
  type Ran (PK j) (PK f) = PK (R.Ran (OP j) f)
  ran = Prof \(j :.: r) -> R.runRan j r
  ranUniv (Prof n) = Prof \g -> g // R.Ran \j -> n (j :.: g)

instance (Profunctor f, Profunctor j) => RightKanLift (PK j :: PROFK d c) (PK f :: PROFK e c) where
  type Rift (PK j) (PK f) = PK (R.Rift (OP j) f)
  rift = Prof \(r :.: j) -> R.runRift j r
  riftUniv (Prof n) = Prof \g -> g // R.Rift \j -> n (g :.: j)