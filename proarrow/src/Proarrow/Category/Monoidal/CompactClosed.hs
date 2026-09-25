{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

-- | Compact closed categories: star-autonomous categories whose dual distributes over the tensor
-- ('distribDual', 'dualUnit'), so that every object has a duality unit and counit ('dualityUnit',
-- 'dualityCounit') and every morphism @x ** u ~> y ** u@ has a trace ('traceCC').
module Proarrow.Category.Monoidal.CompactClosed where

import Data.Kind (Constraint)
import Prelude (($))
import Prelude qualified as P

import Proarrow.Category.Instance.Free (Elems, FREE (..), Free (..), HasStructure (..), Lower, withLowerOb)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , UnitF
  , leftUnitorWith
  , swap
  , unitObj
  , type (**!)
  )
import Proarrow.Category.Monoidal.Action (Act, MonoidalAction (..), actHom)
import Proarrow.Category.Monoidal.Closed (Closed)
import Proarrow.Category.Monoidal.StarAutonomous
  ( DualF
  , StarAutonomous (..)
  , doubleNeg
  , dualObj
  , dualityCounitSA
  , dualityUnitSA
  )
import Proarrow.Category.Monoidal.Strictified (Strictified (..), obj1, swap2, (==))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Tools.Laws (Inverses (..), Labelled (..), Law (..), Laws (..), inverses, (=:=))

class (StarAutonomous k, SymMonoidal k) => CompactClosed k where
  distribDual :: forall (a :: k) b. (Ob a, Ob b) => Dual (a ** b) ~> Dual a ** Dual b
  dualUnit :: Dual (Unit :: k) ~> Unit

dualUnitInv :: forall {k}. (CompactClosed k) => (Unit :: k) ~> Dual Unit
dualUnitInv = leftUnitor @k @(Dual Unit) . dualityUnit @Unit \\ dualObj @(Unit :: k)

dualityUnit :: forall {k} (a :: k). (CompactClosed k, Ob a) => Unit ~> a ** Dual a
dualityUnit = let dualA = dualObj @a in (doubleNeg @a ** dualA) . distribDual @k @(Dual a) @a . dualityUnitSA @a \\ dualA

dualityUnitS :: forall {k} (a :: k). (CompactClosed k, Ob a) => '[] ~> [a, Dual a]
dualityUnitS = withObDual @k @a (Str @'[] @[a, Dual a] (dualityUnit @a))

dualityCounit :: forall {k} (a :: k). (CompactClosed k, Ob a) => Dual a ** a ~> Unit
dualityCounit = dualUnit . dualityCounitSA @a

dualityCounitS :: forall {k} (a :: k). (CompactClosed k, Ob a) => [Dual a, a] ~> '[]
dualityCounitS = withObDual @k @a (Str @[Dual a, a] @'[] (dualityCounit @a))

combineDual :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDual =
  withObDual @k @a $
    withObDual @k @b $
      withOb2 @k @(Dual a) @(Dual b) $
        linDist @k @_ @a @b $
          leftUnitorWith (dualityCounit @a . swap @k @a @(Dual a))
            . associatorInv @k @a @(Dual a) @(Dual b)
            . swap @k @(Dual a ** Dual b) @a

combineDualS :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => '[Dual a, Dual b] ~> '[Dual (a ** b)]
combineDualS =
  withObDual @k @a (withObDual @k @b (withOb2 @k @a @b (withObDual @k @(a ** b) (Str (combineDual @a @b)))))

-- | The dimension of @a@: the trace of its identity, as a scalar.
dimension :: forall {k} (a :: k). (CompactClosed k, Ob a) => (Unit :: k) ~> Unit
dimension = traceCC @a (unitObj ** obj @a)

traceCCS :: forall {k} u (x :: k) y. (CompactClosed k, Ob x, Ob y, Ob u) => [x, u] ~> [y, u] -> '[x] ~> '[y]
traceCCS f =
  withObDual @k @u $
    obj1 @x ** dualityUnitS @u
      == f ** obj1 @(Dual u)
      == obj1 @y ** (swap2 @u @(Dual u) == dualityCounitS @u)

traceCC :: forall {k} u (x :: k) y. (CompactClosed k, Ob x, Ob y, Ob u) => x ** u ~> y ** u -> x ~> y
traceCC f = unStr (traceCCS @u (Str f))

coactCC
  :: forall {m} {k} (t :: (m, k) +-> k) (u :: m) (x :: k) (y :: k)
   . (CompactClosed m, MonoidalAction t, Ob x, Ob y, Ob u) => Act t u x ~> Act t u y -> x ~> y
coactCC f =
  unitor @t @y
    . actHom @t (dualityCounit @u) (obj @y)
    . multiplicatorInv @t @(Dual u) @u @y
    . actHom @t (obj @(Dual u)) f
    . multiplicator @t @(Dual u) @u @x
    . actHom @t (swap @m @u @(Dual u) . dualityUnit @u) (obj @x)
    . unitorInv @t @x
    \\ dualObj @u

instance CompactClosed () where
  distribDual = U.Unit
  dualUnit = U.Unit

instance (CompactClosed j, CompactClosed k) => CompactClosed (j, k) where
  distribDual @'(a, a') @'(b, b') = distribDual @j @a @b :**: distribDual @k @a' @b'
  dualUnit = dualUnit :**: dualUnit

-- | The structures the free category needs for 'CompactClosed', and those its laws are stated for.
type CompactClosedStructures :: [Kind -> Constraint]
type CompactClosedStructures = '[Monoidal, SymMonoidal, Closed, StarAutonomous, CompactClosed]

instance
  (CompactClosedStructures `Elems` cs)
  => HasStructure cs (p :: CAT k) CompactClosed
  where
  data Struct CompactClosed a b where
    DistribDual :: (Ob a, Ob b) => Struct CompactClosed (DualF (a **! b)) (DualF a **! DualF b)
    DualUnit :: Struct CompactClosed (DualF UnitF) UnitF
  foldStructure @f _ (DistribDual @a @b) =
    withLowerOb @f @a (withLowerOb @f @b (distribDual @_ @(Lower f a) @(Lower f b)))
  foldStructure _ DualUnit = dualUnit
instance P.Show (Struct CompactClosed a b) where
  showsPrec _ DistribDual = P.showString "distribDual"
  showsPrec _ DualUnit = P.showString "dualUnit"

instance
  (CompactClosedStructures `Elems` cs)
  => CompactClosed (FREE cs (p :: CAT k))
  where
  distribDual @a @b = St (DistribDual @a @b) Nil
  dualUnit = St DualUnit Nil

-- | 'distribDual' and 'dualUnit' are isomorphisms (so 'Dual' is strong monoidal), and 'dualityUnit'
-- and 'dualityCounit' satisfy the zigzag identities, making @Dual a@ dual to @a@.
instance Laws CompactClosedStructures where
  laws =
    inverses "distribDual" (\ @a @b -> Inverses (distribDual @_ @a @b) (label "combineDual" (combineDual @a @b)))
      P.++ inverses "dualUnit" (Inverses dualUnit (label "dualUnitInv" dualUnitInv))
      P.++ [ Law
               "zigzag (a)"
               \ @a _ ->
                 withObDual @_ @a $
                   ( rightUnitor @_ @a
                       . (obj @a ** label "dualityCounit" (dualityCounit @a))
                       . associator @_ @a @(Dual a) @a
                       . (label "dualityUnit" (dualityUnit @a) ** obj @a)
                       . leftUnitorInv @_ @a
                   )
                     =:= id
           , Law
               "zigzag (Dual a)"
               \ @a _ ->
                 withObDual @_ @a $
                   ( leftUnitor @_ @(Dual a)
                       . (label "dualityCounit" (dualityCounit @a) ** obj @(Dual a))
                       . associatorInv @_ @(Dual a) @a @(Dual a)
                       . (obj @(Dual a) ** label "dualityUnit" (dualityUnit @a))
                       . rightUnitorInv @_ @(Dual a)
                   )
                     =:= id
           ]
