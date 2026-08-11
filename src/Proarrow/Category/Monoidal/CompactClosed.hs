{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Proarrow.Category.Monoidal.CompactClosed where

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , associator
  , leftUnitorWith
  , rightUnitorWith
  , swap
  , unitObj
  )
import Proarrow.Category.Monoidal.Action (Act, MonoidalAction (..), actHom)
import Proarrow.Category.Monoidal.StarAutonomous
  ( StarAutonomous (..)
  , doubleNeg
  , dualObj
  , dualityCounitSA
  , dualityUnitSA
  )
import Proarrow.Category.Monoidal.Strictified (Strictified (..), obj1, swap2, (==))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (//), type (+->))

class (StarAutonomous k, SymMonoidal k) => CompactClosed k where
  distribDual :: forall (a :: k) b. (Ob a, Ob b) => Dual (a ** b) ~> Dual a ** Dual b
  dualUnit :: Dual (Unit :: k) ~> Unit

distribDualInv :: forall {k} (a :: k) b. (CompactClosed k, Ob a, Ob b) => Dual a ** Dual b ~> Dual (a ** b)
distribDualInv =
  dualObj @a //
    dualObj @b //
      let sw = swap @k @(Dual a) @(Dual b)
      in linDist @k @(Dual b ** Dual a) @a @b (rightUnitorWith (dualityCounit @a) . associator @k @(Dual b) @(Dual a) @a) . sw
           \\ sw

dualUnitInv :: forall {k}. (CompactClosed k) => (Unit :: k) ~> Dual Unit
dualUnitInv = leftUnitor @k @(Dual Unit) . dualityUnit @Unit \\ dualObj @(Unit :: k)

dualityUnit :: forall {k} (a :: k). (CompactClosed k, Ob a) => Unit ~> a ** Dual a
dualityUnit = let dualA = dualObj @a in (doubleNeg @a ** dualA) . distribDual @k @(Dual a) @a . dualityUnitSA @a \\ dualA

dualityUnitS :: forall {k} (a :: k). (CompactClosed k, Ob a) => '[] ~> [a, Dual a]
dualityUnitS = Str @'[] @[a, Dual a] (dualityUnit @a)

dualityCounit :: forall {k} (a :: k). (CompactClosed k, Ob a) => Dual a ** a ~> Unit
dualityCounit = dualUnit . dualityCounitSA @a

dualityCounitS :: forall {k} (a :: k). (CompactClosed k, Ob a) => [Dual a, a] ~> '[]
dualityCounitS = Str @[Dual a, a] @'[] (dualityCounit @a)

combineDual :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDual =
  withOb2 @k @(Dual a) @(Dual b)
    ( linDist @k @_ @a @b
        ( leftUnitorWith (dualityCounit @a . swap @k @a @(Dual a))
            . associatorInv @k @a @(Dual a) @(Dual b)
            . swap @k @(Dual a ** Dual b) @a
        )
    )

combineDualS :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => '[Dual a, Dual b] ~> '[Dual (a ** b)]
combineDualS = withOb2 @k @a @b (Str (combineDual @a @b))

dimension :: forall {k} (a :: k). (CompactClosed k, Ob a) => (Unit :: k) ~> Unit
dimension = traceCC @Unit (unitObj ** unitObj)

traceCCS :: forall {k} u (x :: k) y. (CompactClosed k, Ob x, Ob y, Ob u) => [x, u] ~> [y, u] -> '[x] ~> '[y]
traceCCS f =
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
