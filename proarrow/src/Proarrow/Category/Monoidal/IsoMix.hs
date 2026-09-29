{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Isomix categories: *-autonomous categories whose two units agree, @'Dual' 'Unit'@, the unit of
-- par, being isomorphic to 'Unit' ('dualUnit'). Then a dual and its object can be joined into the
-- unit of the tensor, not just into the unit of par. Every compact closed category is isomix, and
-- so is 'Proarrow.Category.Instance.Linear.LINEAR', where tensor and par still differ.
module Proarrow.Category.Monoidal.IsoMix where

import Data.Kind (Constraint)
import Prelude qualified as P

import Proarrow.Category.Instance.Free (Elems, FREE (..), Free (..), HasStructure (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal, UnitF, type (**))
import Proarrow.Category.Monoidal.Closed (Closed)
import Proarrow.Category.Monoidal.StarAutonomous (DualF, StarAutonomous (..), dualityCounitSA)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Promonad (..))
import Proarrow.Tools.Laws (Inverses (..), Law (..), Laws (..), inverses, (===))

class (StarAutonomous k) => IsoMix k where
  -- | The unit of par is isomorphic to the unit of the tensor.
  dualUnit :: Dual (Unit :: k) ~> Unit

  -- | The inverse of 'dualUnit'.
  dualUnitInv :: (Unit :: k) ~> Dual Unit

  -- | Join a dual and its object into the unit. 'dualityCounitDefault' gives it from the
  -- *-autonomous structure; a compact closed category has a counit of its own. (There is no
  -- default method: @a@ occurs only under type families, so GHC could not instantiate one.)
  dualityCounit :: (Ob (a :: k)) => Dual a ** a ~> Unit

-- | 'dualityCounit' from the *-autonomous structure: into the unit of par, then 'dualUnit'.
dualityCounitDefault :: forall {k} (a :: k). (IsoMix k, Ob a) => Dual a ** a ~> Unit
dualityCounitDefault = dualUnit . dualityCounitSA @a

instance IsoMix () where
  dualUnit = U.Unit
  dualUnitInv = U.Unit
  dualityCounit = U.Unit

instance (IsoMix j, IsoMix k) => IsoMix (j, k) where
  dualUnit = dualUnit :**: dualUnit
  dualUnitInv = dualUnitInv :**: dualUnitInv
  dualityCounit @'(a, a') = dualityCounit @j @a :**: dualityCounit @k @a'

-- | The structures the free category needs for 'IsoMix', and those its laws are stated for.
type IsoMixStructures :: [Kind -> Constraint]
type IsoMixStructures = '[Monoidal, SymMonoidal, Closed, StarAutonomous, IsoMix]

instance (IsoMixStructures `Elems` cs) => HasStructure cs (p :: CAT k) IsoMix where
  data Struct IsoMix a b where
    DualUnit :: Struct IsoMix (DualF UnitF) UnitF
    DualUnitInv :: Struct IsoMix UnitF (DualF UnitF)
  foldStructure _ DualUnit = dualUnit
  foldStructure _ DualUnitInv = dualUnitInv
instance P.Show (Struct IsoMix a b) where
  showsPrec _ DualUnit = P.showString "dualUnit"
  showsPrec _ DualUnitInv = P.showString "dualUnitInv"

instance (IsoMixStructures `Elems` cs) => IsoMix (FREE cs (p :: CAT k)) where
  dualUnit = St DualUnit Nil
  dualUnitInv = St DualUnitInv Nil
  dualityCounit @a = dualityCounitDefault @a

-- | 'dualUnit' and 'dualUnitInv' are inverses, and 'dualityCounit' is the one from the
-- *-autonomous structure.
instance Laws IsoMixStructures where
  laws =
    inverses "dualUnit" (Inverses dualUnit dualUnitInv)
      P.++ [Law "dualityCounit definition" \ @a _ -> withObDual @_ @a (dualityCounit @_ @a === dualityCounitDefault @a)]
