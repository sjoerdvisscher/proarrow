{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Free where

import Test.Falsify.Generator (choose)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (fst, id, snd, (.))

import Proarrow.Category.Instance.Free (FREE (..), Free (..))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), type (+))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), (&&&), type (*!))
import Proarrow.Object.Initial (HasInitialObject (..), InitF)
import Proarrow.Object.Terminal (HasTerminalObject (..), TermF)
import Proarrow.Profunctor.Initial (InitialProfunctor)

import Props
import Testable (GenTotal (..), Testable (..), TestableType (..), genObDef, one, pattern GenNonEmpty)

type FREEKIND =
  FREE '[HasInitialObject, HasTerminalObject, HasBinaryProducts, HasBinaryCoproducts] (InitialProfunctor :: CAT ())

test :: TestTree
test =
  testGroup
    "Free"
    [ propCategory @FREEKIND
    -- , propTerminalObject @FREEKIND
    -- , propInitialObject @FREEKIND
    -- , propBinaryProducts @FREEKIND (\r -> r)
    -- , propBinaryCoproducts @FREEKIND (\r -> r)
    -- , propClosed @FREEKIND (\r -> r) (\r -> r)
    ]

instance Testable FREEKIND where
  type TestOb a = TestObFree a
  genOb = genObDef @'[TermF, TermF + TermF, (TermF + TermF) *! (TermF + TermF)]
  showOb @a = showObFree @a

instance (TestObFree a, TestObFree b) => TestableType (Free a (b :: FREEKIND)) where
  gen = genFree

class (Ob a) => TestObFree (a :: FREEKIND) where
  genFree :: (TestObFree b) => GenTotal (Free a b)
  genFreeTerm :: GenTotal (Free TermF a)
  showObFree :: String
instance TestObFree InitF where
  genFree = one initiate
  genFreeTerm = GenEmpty undefined
  showObFree = "InitF"
instance TestObFree TermF where
  genFree = genFreeTerm
  genFreeTerm = one id
  showObFree = "TermF"
instance (TestObFree a, TestObFree b) => TestObFree (a + b) where
  genFree @c = case (genFree @a @c, genFree @b @c) of
    (GenEmpty l, _) -> GenEmpty (l . (. lft))
    (_, GenEmpty r) -> GenEmpty (r . (. rgt))
    (GenNonEmpty gl, GenNonEmpty gr) -> GenNonEmpty (liftA2 (|||) gl gr)
  genFreeTerm = case (genFreeTerm @a, genFreeTerm @b) of
    (GenEmpty _, GenEmpty _) -> GenEmpty undefined
    (GenNonEmpty gl, GenEmpty _) -> GenNonEmpty ((lft .) <$> gl)
    (GenEmpty _, GenNonEmpty gr) -> GenNonEmpty ((rgt .) <$> gr)
    (GenNonEmpty gl, GenNonEmpty gr) -> GenNonEmpty (choose ((lft .) <$> gl) ((rgt .) <$> gr))
  showObFree = "(" ++ showObFree @a ++ " + " ++ showObFree @b ++ ")"
instance (TestObFree a, TestObFree b) => TestObFree (a *! b) where
  genFree @c = case (genFree @a @c, genFree @b @c) of
    (GenEmpty _, GenEmpty _) -> GenEmpty undefined
    (GenNonEmpty gl, _) -> GenNonEmpty ((. fst) <$> gl)
    (_, GenNonEmpty gr) -> GenNonEmpty ((. snd) <$> gr)
  genFreeTerm = case (genFreeTerm @a, genFreeTerm @b) of
    (GenEmpty l, _) -> GenEmpty (\t -> l (fst . t))
    (_, GenEmpty r) -> GenEmpty (\t -> r (snd . t))
    (GenNonEmpty gl, GenNonEmpty gr) -> GenNonEmpty (liftA2 (&&&) gl gr)
  showObFree = "(" ++ showObFree @a ++ " *! " ++ showObFree @b ++ ")"
