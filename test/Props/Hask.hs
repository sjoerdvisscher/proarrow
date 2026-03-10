{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Hask where

import Data.Kind (Type)
import Data.Void (Void)
import Test.Falsify.Generator (Function, choose, elem, fun, function, minimalValue)
import Test.Falsify.Property (Property, genWith)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Prelude hiding (elem)

import Props
import Testable (GenTotal (..), Testable (..), TestableType (..), genObDef, one, optGen, pattern GenNonEmpty)

test :: TestTree
test =
  testGroup
    "Hask"
    [ propCategory @Type
    , propTerminalObject @Type
    , propInitialObject @Type
    , propBinaryProducts @Type (\r -> r)
    , propBinaryCoproducts @Type (\r -> r)
    , propClosed @Type (\r -> r) (\r -> r)
    , propMonoid @[()] (\r -> r)
    ]

instance Testable Type where
  type TestOb a = (TestableType a, Typeable a, Function a)
  showOb @a = show (typeRep @a)
  genOb = genObDef @'[Bool, (Bool, Bool), Maybe Bool, Void]

instance (TestOb a, TestOb b) => TestableType (a -> b) where
  gen = case gen @b of
    GenEmpty absurd -> case gen @a of
      GenEmpty absurda -> one absurda
      GenNonEmpty g -> GenEmpty \ab -> absurd (ab (minimalValue g))
    GenNonEmpty gb -> GenFun id (fun gb)
  eqP = eqHask
  showP _ = "<function>"

eqHask :: (TestableType a, TestableType b) => (a -> b) -> (a -> b) -> Property Bool
eqHask l r =
  case gen of
    GenEmpty _ -> pure True -- There can only be one function of a type with no values
    GenNonEmpty ga -> do
      a <- genWith (Just . showP) ga
      eqP (l a) (r a)

instance TestableType Bool where
  gen = optGen [False, True]
instance TestableType () where
  gen = one ()
instance TestableType Void where
  gen = GenEmpty \case {}
  eqP = \case {}
  showP = \case {}

instance (TestableType a, TestableType b) => TestableType (a, b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty f, _) -> GenEmpty (f . fst)
    (_, GenEmpty g) -> GenEmpty (g . snd)
    (GenNonEmpty ga, GenNonEmpty gb) -> GenNonEmpty (liftA2 (,) ga gb)
  eqP (l1, l2) (r1, r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (a, b) = "(" ++ showP a ++ ", " ++ showP b ++ ")"

instance (TestableType a, TestableType b) => TestableType (Either a b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty f, GenEmpty g) -> GenEmpty (either f g)
    (GenNonEmpty ga, GenEmpty _) -> GenNonEmpty (Left <$> ga)
    (GenEmpty _, GenNonEmpty gb) -> GenNonEmpty (Right <$> gb)
    (GenNonEmpty ga, GenNonEmpty gb) -> GenNonEmpty (choose (Left <$> ga) (Right <$> gb))
  eqP (Left l) (Left r) = eqP l r
  eqP (Right l) (Right r) = eqP l r
  eqP _ _ = pure False
  showP (Left a) = "Left " ++ showP a
  showP (Right b) = "Right " ++ showP b

instance (TestableType a) => TestableType (Maybe a) where
  gen = case gen @a of
    GenEmpty _ -> one Nothing
    GenNonEmpty ga -> GenNonEmpty (choose (pure Nothing) (Just <$> ga))
  eqP Nothing Nothing = pure True
  eqP (Just l) (Just r) = eqP l r
  eqP _ _ = pure False
  showP Nothing = "Nothing"
  showP (Just a) = "Just " ++ showP a

instance TestableType [()] where
  gen = GenNonEmpty (elem [[], [()], [(), ()], [(), (), ()]])

-- Hard to write and also unused instances.
instance Function (a -> b) where
  function = error "Should not be used"
