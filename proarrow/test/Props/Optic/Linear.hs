-- | Running optics in the __non-cartesian__ @LINEAR@ category.
--
-- In @LINEAR@ the monoidal tensor @('**')@ is @(,)@ while the categorical product @('&&')@ is
-- @With@ (linear logic's additive conjunction), so @tensor ≠ product@ and @LINEAR@ is /not/
-- 'Proarrow.Limit.BinaryProduct.Cartesian'. These optics therefore only build and run because the
-- optic constraints were loosened off @Cartesian@: 'over' on a 'Setter' needs no @Bicartesian@,
-- and a lens's @'Proarrow.Profunctor.Representable.Rep' ('Proarrow.Limit.BinaryProduct.Product' s)@
-- witness needs only 'Proarrow.Limit.BinaryProduct.HasBinaryProducts', not @tensor = product@.
module Props.Optic.Linear (test) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude (Bool (..), ($))

import Proarrow.Category.Instance.Linear (LINEAR (..), Linear (..), mkWith, unLinear)
import Proarrow.Category.Monoidal (type (**))
import Proarrow.Core (Promonad (..), type (~>))
import Proarrow.Limit.BinaryProduct (fst, snd, (&&&), type (&&))
import Proarrow.Optic.Getter (view)
import Proarrow.Optic.Lens (Lens, lens)
import Proarrow.Optic.MonoidalLens (MonoidalLens, monLens)
import Proarrow.Optic.Setter (over)
import Proarrow.Optic.Traversal (traverseOf)
import Proarrow.Profunctor.Instance.Identity (Id (..))

import Props.Optic.Hask (assertEq)

-- | The @_1@ lens over @LINEAR@: focus the first component of the additive product @With@.
-- Built exactly like Hask's @_1@ (@'lens' 'fst' put@), but the product here is @With@, not a tuple.
_wfst :: Lens (L Bool && L Bool) (L Bool && L Bool) (L Bool) (L Bool)
_wfst = lens fst (snd &&& (snd . fst))

-- | Negation as a linear morphism.
notL :: L Bool ~> L Bool
notL = Linear \case True -> False; False -> True

-- | A __monoidal lens__ onto the second component of a @LINEAR@ tensor pair @L Bool '**' L Bool@.
-- Because @L Bool@ is a 'Proarrow.Monoid.Comonoid' (a @Bool@ is copied\/discarded by case-analysis,
-- which is linear), this is a genuine lens in a non-cartesian category: it both sets /and/ views,
-- viewing by discarding the (comonoidal) first-component residual.
_2mon :: MonoidalLens (L Bool ** L Bool) (L Bool ** L Bool) (L Bool) (L Bool)
_2mon = monLens @(L Bool) id id

test :: TestTree
test =
  testGroup
    "Proarrow.OpticLinear"
    [ testProperty "over a lens in LINEAR (product = With, tensor = (,), so non-cartesian)" $
        assertEq (unLinear (over _wfst notL) (mkWith True False)) (mkWith False False)
    , testProperty "over leaves the unfocused component alone" $
        assertEq (unLinear (over _wfst notL) (mkWith True True)) (mkWith False True)
    , testProperty "view a lens in LINEAR" $
        assertEq (unLinear (view _wfst) (mkWith True False)) True
    , -- exercises travP's  act @ProdAction @(PR s)  over a category where tensor /= product
      testProperty "traverseOf a lens in LINEAR (distributes Id via the product action)" $
        assertEq (unLinear (unId (traverseOf _wfst (Id notL))) (mkWith True False)) (mkWith False False)
    , -- a genuine monoidal lens in LINEAR: L Bool is a comonoid, so it sets and views
      testProperty "over a MonoidalLens in LINEAR (modify the tensor focus)" $
        assertEq (unLinear (over _2mon notL) (True, False)) (True, True)
    , testProperty "view a MonoidalLens in LINEAR (discard the comonoidal residual)" $
        assertEq (unLinear (view _2mon) (True, False)) False
    ]
