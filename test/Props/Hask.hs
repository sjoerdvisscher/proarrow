{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Hask where

import Data.Kind (Type)
import Data.Void (Void)
import Test.Falsify.Generator (Function, choose, elem, function)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Prelude hiding (elem)

import Props
import Testable
  ( GenTotal (..)
  , Testable (..)
  , TestableType (..)
  , TestingEqShow (..)
  , genObDef
  , one
  , optGen
  , pattern GenNonEmpty
  )

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
    , testMonoid @[()] (\r -> r)
    ]

instance Testable Type where
  type TestOb a = (TestableType a, Typeable a, Function a)
  showOb @a = show (typeRep @a)
  genOb = genObDef @'[Bool, (Bool, Bool), Maybe Bool, Void]

instance TestableType Bool where
  gen = optGen [False, True]
instance TestableType () where
  gen = one ()
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
    GenEmpty _ -> one Nothing
    GenNonEmpty ga -> GenNonEmpty (choose (pure Nothing) (Just <$> ga))
instance (TestingEqShow a) => TestingEqShow (Maybe a) where
  eqP Nothing Nothing = pure True
  eqP (Just l) (Just r) = eqP l r
  eqP _ _ = pure False
  showP Nothing = "Nothing"
  showP (Just a) = "Just " ++ showP a

instance TestingEqShow [()]
instance TestableType [()] where
  gen = GenNonEmpty (elem [[], [()], [(), ()], [(), (), ()]])

-- Hard to write and also unused instances.
instance Function (a -> b) where
  function = error "Should not be used"
