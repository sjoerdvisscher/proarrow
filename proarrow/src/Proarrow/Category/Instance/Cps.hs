{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A closed symmetric monoidal category with a chosen answer object @r@ is a dialogue category,
-- with @'Dual' a = a '~~>' r@. 'CPS' wraps the category to say which object. The morphisms are
-- those of the category itself, so with @r@ an object of effects, as @IO ()@ in 'Data.Kind.Type',
-- a morphism is pure and a term of @'Proarrow.Tools.SMC.Up' a@ is a computation
-- @(a -> IO ()) -> IO ()@: call by push value, with the effects in the computations only.
--
-- @CPS r@ is isomix exactly when @r@ is the unit ('answerUnit'), and *-autonomous only in
-- degenerate cases, since @(a ~~> r) ~~> r@ is rarely @a@.
module Proarrow.Category.Instance.Cps (CPS (..), Cps (..), answerUnit) where

import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Closed (Closed (..), swapClosed, toEl, uncurry)
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..))
import Proarrow.Category.Monoidal.IsoMix (IsoMix (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, WrappedOb, dimapDefault, obj)
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..))
import Proarrow.Optic (PIso', iso)

type data CPS (r :: k) = C k

-- | The arrows of the category, wrapped as a category on the 'CPS'-wrapped kind.
type Cps :: CAT (CPS r)
data Cps (a :: CPS r) b where
  Cps :: {unCps :: a ~> b} -> Cps (C a :: CPS r) (C b)

instance (CategoryOf k) => Profunctor (Cps :: CAT (CPS (r :: k))) where
  dimap = dimapDefault
  r \\ Cps f = r \\ f

instance (CategoryOf k) => Promonad (Cps :: CAT (CPS (r :: k))) where
  id = Cps id
  Cps f . Cps g = Cps (f . g)

instance (CategoryOf k) => CategoryOf (CPS (r :: k)) where
  type (~>) = Cps
  type Ob a = WrappedOb C a

instance (Monoidal k) => MonoidalProfunctor (Cps :: CAT (CPS (r :: k))) where
  one = Cps one
  Cps f ** Cps g = Cps (f ** g)

instance (Monoidal k) => Monoidal (CPS (r :: k)) where
  type Unit = C Unit
  type a ** b = C (UN C a ** UN C b)
  withOb2 @(C a) @(C b) r = withOb2 @k @a @b r
  leftUnitor @(C a) = Cps (leftUnitor @k @a)
  leftUnitorInv @(C a) = Cps (leftUnitorInv @k @a)
  rightUnitor @(C a) = Cps (rightUnitor @k @a)
  rightUnitorInv @(C a) = Cps (rightUnitorInv @k @a)
  associator @(C a) @(C b) @(C c) = Cps (associator @k @a @b @c)
  associatorInv @(C a) @(C b) @(C c) = Cps (associatorInv @k @a @b @c)

instance (SymMonoidal k) => SymMonoidal (CPS (r :: k)) where
  swap @(C a) @(C b) = Cps (swap @k @a @b)

instance (Closed k) => Closed (CPS (r :: k)) where
  type a ~~> b = C (UN C a ~~> UN C b)
  withObExp @(C a) @(C b) r = withObExp @k @a @b r
  curry @(C a) @(C b) (Cps f) = Cps (curry @k @a @b f)
  apply @(C a) @(C b) = Cps (apply @k @a @b)
  Cps f ^^^ Cps g = Cps (f ^^^ g)

-- | The dual of @a@ is @a '~~>' r@, the functor 'Proarrow.Category.Monoidal.Closed.Not' @r@ on
-- objects: linear distribution is uncurrying, reassociating and currying.
instance (Closed k, SymMonoidal k, Ob r) => Dialogue (CPS (r :: k)) where
  type Dual (a :: CPS r) = C (UN C a ~~> r)
  withObDual @(C a) r' = withObExp @k @a @r r'
  dual (Cps f) = Cps (obj @r ^^^ f)
  linDist @(C a) @(C b) @(C c) (Cps f) =
    withOb2 @k @b @c (Cps (curry @k @a @(b ** c) (uncurry @c @r f . associatorInv @k @a @b @c)))
  linDistInv @(C a) @(C b) @(C c) (Cps f) =
    withOb2 @k @a @b (withOb2 @k @b @c (Cps (curry @k @(a ** b) @c (uncurry @(b ** c) @r f . associator @k @a @b @c))))
  doubleNegInv @(C a) = withObExp @k @a @r (Cps (swapClosed @r (obj @(a ~~> r))))

-- | With the unit as the answer object, @'Dual' 'Unit' = Unit ~~> Unit ≅ Unit@, and a consumer meets
-- its value in 'apply'. With any other answer object the units differ, so this is the only isomix
-- instance; the constraint on @r@ says so, since 'Unit' is a type family and cannot head an
-- instance.
instance (Closed k, SymMonoidal k, r ~ Unit) => IsoMix (CPS (r :: k)) where
  dualUnit = withObExp @k @Unit @Unit (Cps (apply @k @Unit @Unit . rightUnitorInv @k @(Unit ~~> Unit)))
  dualUnitInv = Cps (toEl @Unit)
  dualityCounit @(C a) = Cps (apply @k @a @Unit)

-- | The converse: an isomix structure on @CPS r@ makes @r@ the unit, through @Unit ~~> r ≅ r@.
answerUnit :: forall {k} (r :: k). (Closed k, Ob r, IsoMix (CPS r)) => PIso' r Unit
answerUnit =
  withObExp @k @Unit @r
    ( iso
        (unCps (dualUnit @(CPS r)) . toEl @r)
        (apply @k @Unit @r . rightUnitorInv @k @(Unit ~~> r) . unCps (dualUnitInv @(CPS r)))
    )

instance (Comonoid a) => Comonoid (C a :: CPS r) where
  counit = Cps counit
  comult = Cps comult

instance (CocommutativeComonoid a) => CocommutativeComonoid (C a :: CPS r)
