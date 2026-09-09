{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Hask where

import Data.Kind (Type)
import Data.List (intercalate)
import Data.Void (Void)
import Proarrow.Category.Instance.Opposite (OPPOSITE)
import Proarrow.Category.Monoidal.Closed (ExpRep)
import Proarrow.Functor (Prelude (..))
import Proarrow.Profunctor.Instance.Costar (Costar, unCostar, pattern Costar)
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (Rep)
import Test.Falsify.Generator (Function, choose, function, functionMap, list)
import Test.Falsify.Range (between)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Prelude hiding (elem, (.))

import Control.Monad (unless)
import Proarrow.Core (Promonad (..), type (+->))
import Proarrow.Monoid qualified as Monoid
import Proarrow.Testing
  ( GenTotal (..)
  , TestOb'
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , invmap
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
    , testFrobenius @() (\r -> r)
    , testProperty "list monoid is not Frobenius: copy-comonoid breaks speciality" $
        unless
          ((Monoid.mappend . Monoid.comult @[()]) [()] /= [()])
          (testFailed "speciality unexpectedly held for [()]")
    , testProfunctor @(Rep (ExpRep :: (OPPOSITE Type, Type) +-> Type))
    , testRepresentable @(Star (Prelude Maybe) :: Type +-> Type) (\r -> r)
    , testCorepresentable @(Costar (Prelude Maybe) :: Type +-> Type) (\r -> r)
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

instance (TestableType (f a)) => TestableType (Prelude f a) where
  gen = invmap Prelude unPrelude gen
instance (TestingEqShow (f a)) => TestingEqShow (Prelude f a) where
  eqP (Prelude l) (Prelude r) = eqP l r
  showP (Prelude f) = showP f
instance (Function (f a)) => Function (Prelude f a) where
  function = fmap (functionMap unPrelude Prelude) . function

instance (Functor f, Typeable f, Typeable b, TestOb a, TestOb (f b)) => TestableType (Star (Prelude f) a b) where
  gen = invmap Star unStar gen
instance (Functor f, Typeable f, Typeable b, TestOb a, TestOb (f b)) => TestingEqShow (Star (Prelude f) a b) where
  eqP (Star l) (Star r) = eqP l r
  showP (Star f) = showP f
instance (Functor f, Typeable f, forall b. (TestOb b) => TestOb' (f b)) => TestableProfunctor (Star (Prelude f))

instance (Functor f, Typeable f, Typeable a, TestOb (f a), TestOb b) => TestableType (Costar (Prelude f) a b) where
  gen = invmap Costar unCostar gen
instance (Functor f, Typeable f, Typeable a, TestOb (f a), TestOb b) => TestingEqShow (Costar (Prelude f) a b) where
  eqP (Costar l) (Costar r) = eqP l r
  showP (Costar f) = showP f
instance (Functor f, Typeable f, forall b. (TestOb b) => TestOb' (f b)) => TestableProfunctor (Costar (Prelude f))
