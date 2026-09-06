-- | Running optics in the __non-cartesian__ @FINREL@ category (the category of relations between
-- finite sets), which is 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' but /not/
-- 'Proarrow.Limit.Terminal.Semicartesian' (its monoidal unit @FR 1@ is not the terminal object
-- @FR 0@). Folding a prism must discard the non-matching residual; that discard now comes from
-- 'Proarrow.Category.Monoidal.CopyDiscard.discard' rather than @terminate@, so prism/fold optics
-- instantiate here at all -- which they could not while the witnesses required @Semicartesian@.
module Props.Optic.FinRel (test) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)

import Data.Type.Nat (Nat1, Nat2)
import Prelude (($))

import Proarrow.Category.Instance.FinRel (FINREL (..), FinRel, unFinRel)
import Proarrow.Category.Monoidal.CopyDiscard (discard)
import Proarrow.Colimit.BinaryCoproduct ((|||))
import Proarrow.Core (Promonad (..), (.))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Optic.Fold (foldMapOf)
import Proarrow.Optic.Prism (Prism, prism)

import Props.FinRel ()
import Props.Optic.Hask (assertEq)

-- | A prism onto one summand of @FR 1 || FR 1 = FR 2@. Building it needs only 'discard' (to review
-- the residual away), not products.
prL :: Prism (FR Nat2) (FR Nat1) (FR Nat1) (FR Nat1)
prL = prism id id

test :: TestTree
test =
  testGroup
    "Proarrow.OpticFinRel"
    [ -- The optic-plumbed fold (Optic -> Forget -> Prostrong -> foldMapP) must agree with the
      -- hand-built relation @(mempty . discard ||| id)@: the focus branch reduces via @id@, the
      -- non-matching branch is discarded to @Unit@ and sent to @mempty@.
      testProperty "foldMapOf a prism in FINREL (non-cartesian CopyDiscard; discards the non-match)" $
        assertEq
          (unFinRel (foldMapOf prL (id @FinRel @(FR Nat1))))
          (unFinRel (mempty @(FR Nat1) . discard @FINREL @(FR Nat1) ||| id @FinRel @(FR Nat1)))
    ]
