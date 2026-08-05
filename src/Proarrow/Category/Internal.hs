{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Internal where

import Prelude (($))

import Data.Fin (fin0, fin1, fin2)
import Data.Type.Nat (Nat2, Nat3)
import Data.Vec.Lazy (Vec (..))
import Proarrow.Category.Instance.Bool (BOOL)
import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Core (CategoryOf (..))
import Proarrow.Profunctor.Cone (Cone (..), Cosink (..))

-- | An internal category in a category @k@.
class ik `InternalIn` k where
  type C0 ik :: k
  type C1 ik :: k
  source :: C1 ik ~> (C0 ik :: k)
  target :: C1 ik ~> (C0 ik :: k)
  identity :: C0 ik ~> (C1 ik :: k)
  compose :: Cosink [C1 ik, C1 ik, C1 ik :: k] -- first arrow projection, second arrow projection, composite

-- >>> import Data.Fin
-- >>> import Data.Type.Nat
-- >>> import Data.Vec.Lazy
-- >>> import Proarrow.Limit.Pullback
-- >>> (case pullback (source @BOOL @FINSET) (target @BOOL @FINSET) of Cone (Leg (FinSet l) (Leg (FinSet r) Apex)) -> P.show (l, r)) :: P.String
-- "(0 ::: 1 ::: 2 ::: 2 ::: VNil,0 ::: 0 ::: 1 ::: 2 ::: VNil)"
instance BOOL `InternalIn` FINSET where
  type C0 BOOL = FS Nat2 -- Fin0 = FLS, Fin1 = TRU
  type C1 BOOL = FS Nat3 -- Fin0 = Fls, Fin1 = F2T, Fin2 = Tru
  source = FinSet $ fin0 ::: fin0 ::: fin1 ::: VNil
  target = FinSet $ fin0 ::: fin1 ::: fin1 ::: VNil
  identity = FinSet $ fin0 ::: fin2 ::: VNil

  -- 4 different ways to compose, read vertically.
  compose =
    Cone $
      Leg (FinSet $ fin0 ::: fin1 ::: fin2 ::: fin2 ::: VNil) $
        Leg (FinSet $ fin0 ::: fin0 ::: fin1 ::: fin2 ::: VNil) $
          Leg
            (FinSet $ fin0 ::: fin1 ::: fin1 ::: fin2 ::: VNil)
            Apex

-- | A finite category is an internal category in @FINSET@.
type Finite k = k `InternalIn` FINSET
