{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Hask where

import Data.Kind (Type)
import Data.List (intercalate)
import Data.Void (Void)
import Proarrow.Category.Instance.Opposite (OPPOSITE)
import Proarrow.Category.Monoidal.Closed (ExpRep)
import Proarrow.Profunctor.Representable (Rep)
import Test.Falsify.Generator (Function, choose, function, list)
import Test.Falsify.Range (between)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Prelude hiding (elem, (.))

import Control.Monad (unless)
import Proarrow.Core (Promonad (..), type (+->))
import Proarrow.Monoid qualified as Monoid
import Proarrow.Testing
  ( GenTotal (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , oneElem
  , optGen
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Test.Tasty.Falsify (testFailed, testProperty)

test :: TestTree
test =
  testGroup
    "Hask"
    [ propCategory @Type
    , propTerminalObject @Type
    , propInitialObject @Type
    , propBinaryProducts @Type (\r -> r)
    , propBinaryCoproducts @Type (\r -> r)
    , propDistributive @Type (\r -> r) (\r -> r)
    , propClosed @Type (\r -> r) (\r -> r)
    , -- the unit is (trivially) Frobenius, but a non-trivial monoid with the cartesian copy
      -- comonoid is only a bialgebra: speciality already fails, so this is a deterministic
      -- counterexample rather than a randomized property (see also the note in 'propFrobenius')
      testFrobenius @() (\r -> r)
    , testProperty "list monoid is not Frobenius: copy-comonoid breaks speciality" $
        unless
          ((Monoid.mappend . Monoid.comult @[()]) [()] /= [()])
          (testFailed "speciality unexpectedly held for [()]")
    , -- a 'FunctorForRep' (here the exponential @(a, b) |-> a -> b@) is tested as the profunctor
      -- 'Rep' of it: the profunctor laws on @Rep f@ are the functoriality of @f@
      testProfunctor @(Rep (ExpRep :: (OPPOSITE Type, Type) +-> Type))
    ]

instance Testable Type where
  type TestOb a = (TestableType a, Typeable a, Function a)
  showOb @a = show (typeRep @a)
  genSome = genSomeDef @'[Bool, (Bool, Bool), Maybe Bool, Void]

instance TestableProfunctor (->)

instance TestableType Bool where
  gen = optGen [False, True]
instance TestableType () where
  gen = oneElem ()
instance TestableType Void where
  gen = GenEmpty \case {}
instance TestingEqShow Bool
instance TestingEqShow ()
instance TestingEqShow Void

instance (TestableType a, TestableType b) => TestableType (a, b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty f, _) -> GenEmpty (f . fst)
    (_, GenEmpty g) -> GenEmpty (g . snd)
    (GenNonEmpty ga, GenNonEmpty gb) -> GenNonEmpty (liftA2 (,) ga gb)
instance (TestingEqShow a, TestingEqShow b) => TestingEqShow (a, b) where
  eqP (l1, l2) (r1, r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (a, b) = "(" ++ showP a ++ ", " ++ showP b ++ ")"

instance (TestableType a, TestableType b) => TestableType (Either a b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty f, GenEmpty g) -> GenEmpty (either f g)
    (GenNonEmpty ga, GenEmpty _) -> GenNonEmpty (Left <$> ga)
    (GenEmpty _, GenNonEmpty gb) -> GenNonEmpty (Right <$> gb)
    (GenNonEmpty ga, GenNonEmpty gb) -> GenNonEmpty (choose (Left <$> ga) (Right <$> gb))
instance (TestingEqShow a, TestingEqShow b) => TestingEqShow (Either a b) where
  eqP (Left l) (Left r) = eqP l r
  eqP (Right l) (Right r) = eqP l r
  eqP _ _ = pure False
  showP (Left a) = "Left " ++ showP a
  showP (Right b) = "Right " ++ showP b

instance (TestableType a) => TestableType (Maybe a) where
  gen = case gen @a of
    GenEmpty _ -> oneElem Nothing
    GenNonEmpty ga -> GenNonEmpty (choose (pure Nothing) (Just <$> ga))
instance (TestingEqShow a) => TestingEqShow (Maybe a) where
  eqP Nothing Nothing = pure True
  eqP (Just l) (Just r) = eqP l r
  eqP _ _ = pure False
  showP Nothing = "Nothing"
  showP (Just a) = "Just " ++ showP a

instance (TestingEqShow a) => TestingEqShow [a] where
  eqP l r = if length l /= length r then pure False else foldr (liftA2 (&&)) (pure True) (zipWith eqP l r)
  showP xs = "[" ++ intercalate ", " (map showP xs) ++ "]"
instance (TestableType a) => TestableType [a] where
  gen = case gen @a of
    GenEmpty _ -> GenNonEmpty (pure [])
    GenNonEmpty g -> GenNonEmpty (list (between (0, 4)) g)

-- Hard to write and also unused instances.
instance Function (a -> b) where
  function = error "Should not be used"

instance TestableProfunctor (Rep (ExpRep :: (OPPOSITE Type, Type) +-> Type))
