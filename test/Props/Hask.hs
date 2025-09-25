{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Hask where

import Control.Monad (replicateM)
import Data.Kind (Type)
import Data.List (intercalate)
import Data.Void (Void)
import Test.Falsify.Generator (Function, applyFun, choose, fun, function)
import Test.Falsify.Property (genWith)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Prelude

import Props
import Testable (EnumAll (..), GenTotal (..), Testable (..), TestableType (..), genObDef, one)

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
    ]

instance Testable Type where
  type TestOb a = (TestableType a, Typeable a, EnumAll a, Function a, Eq a)
  showOb @a = show (typeRep @a)
  genOb = genObDef @'[Bool, (Bool, Bool), Maybe Bool]

instance EnumAll Void where
  enumAll = []
instance EnumAll () where
  enumAll = [()]
instance EnumAll Bool where
  enumAll = [False, True]
instance (EnumAll a, EnumAll b) => EnumAll (a, b) where
  enumAll = [(a, b) | a <- enumAll, b <- enumAll]
instance (EnumAll a, EnumAll b) => EnumAll (Either a b) where
  enumAll = [Left a | a <- enumAll] ++ [Right b | b <- enumAll]
instance (EnumAll a) => EnumAll (Maybe a) where
  enumAll = Nothing : map Just enumAll
instance (Eq a, EnumAll a, EnumAll b) => EnumAll (a -> b) where
  enumAll = do
    let as = enumAll
    table <- zip as <$> replicateM (length as) enumAll
    return \a -> case lookup a table of
      Just b -> b
      Nothing -> error "enumAll @(a -> b): value of type a passed that is not in enumAll @a"
instance (Eq b, EnumAll a) => Eq (a -> b) where
  l == r = all id [l a == r a | a <- enumAll @a]
instance (TestOb a, TestOb b) => TestableType (a -> b) where
  gen = case gen @a of
    GenEmpty absurd -> one absurd
    GenNonEmpty a _ -> case gen @b of
      GenEmpty absurd -> GenEmpty \ab -> absurd (ab a)
      GenNonEmpty b gb -> GenNonEmpty (const b) (fmap applyFun (fun gb))
  eqP l r =
    case gen of
      GenEmpty _ -> pure True -- There can only be one function of a type with no values
      GenNonEmpty _ ga -> do
        a <- genWith (Just . showP) ga
        eqP (l a) (r a)
  showP f = intercalate "," [showP x ++ "->" ++ showP (f x) | x <- enumAll]

instance TestableType Bool
instance TestableType ()
instance TestableType Void where
  gen = GenEmpty \case {}
  eqP = \case {}
  showP = \case {}

instance (TestableType a, TestableType b) => TestableType (a, b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty f, _) -> GenEmpty (f . fst)
    (_, GenEmpty g) -> GenEmpty (g . snd)
    (GenNonEmpty a ga, GenNonEmpty b gb) -> GenNonEmpty (a, b) (liftA2 (,) ga gb)
  eqP (l1, l2) (r1, r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (a, b) = "(" ++ showP a ++ ", " ++ showP b ++ ")"

instance (TestableType a, TestableType b) => TestableType (Either a b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty f, GenEmpty g) -> GenEmpty (either f g)
    (GenNonEmpty a ga, GenEmpty _) -> GenNonEmpty (Left a) (Left <$> ga)
    (GenEmpty _, GenNonEmpty b gb) -> GenNonEmpty (Right b) (Right <$> gb)
    (GenNonEmpty _ ga, GenNonEmpty b gb) -> GenNonEmpty (Right b) (choose (Left <$> ga) (Right <$> gb))
  eqP (Left l) (Left r) = eqP l r
  eqP (Right l) (Right r) = eqP l r
  eqP _ _ = pure False
  showP (Left a) = "Left " ++ showP a
  showP (Right b) = "Right " ++ showP b

instance (TestableType a) => TestableType (Maybe a) where
  gen = case gen @a of
    GenEmpty _ -> one Nothing
    GenNonEmpty a ga -> GenNonEmpty (Just a) (choose (pure Nothing) (Just <$> ga))
  eqP Nothing Nothing = pure True
  eqP (Just l) (Just r) = eqP l r
  eqP _ _ = pure False
  showP Nothing = "Nothing"
  showP (Just a) = "Just " ++ showP a

-- Hard to write and also unused instances.
instance Function (a -> b) where
  function = undefined
instance Function Void where
  function = undefined