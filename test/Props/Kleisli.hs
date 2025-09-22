{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Kleisli where

import Data.Kind (Type)
import Data.Typeable (Typeable)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (id, (.))

import Proarrow.Category.Instance.Free (Show2)
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Prelude (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Star (Star (..))

import GHC.Generics (Generic)
import Props
import Props.Hask ()
import Test.Falsify.Generator (Function (..), functionMap)
import Testable (EnumAll (..), Testable (..), TestableProfunctor, TestableType (..), genObDef, optGen)

test :: TestTree
test =
  testGroup
    "Kleisli"
    [ testGroup
        "Maybe monad"
        [ propCategory @(KLEISLI (Star (Prelude Maybe)))
        , propInitialObject @(KLEISLI (Star (Prelude Maybe)))
        , propMonoidal @(KLEISLI (Star (Prelude Maybe))) (\r -> r)
        , propBinaryCoproducts @(KLEISLI (Star (Prelude Maybe))) (\r -> r)
        ]
    , testGroup
        "Pair comonad"
        [ propCategory @(KLEISLI (Costar (Prelude Pair)))
        , propTerminalObject @(KLEISLI (Costar (Prelude Pair)))
        , propInitialObject @(KLEISLI (Costar (Prelude Pair)))
        , propMonoidal @(KLEISLI (Costar (Prelude Pair))) (\r -> r)
        ]
    ]

instance (TestOb a, TestOb b, Show2 p) => Show (Kleisli a (b :: KLEISLI p)) where
  show (Kleisli f) = show f

instance (TestableProfunctor p, Promonad p, TestOb a, TestOb b) => TestableType (Kleisli (a :: KLEISLI (p :: Type +-> Type)) b) where
  gen = fmap Kleisli <$> gen @(p (UN KL a) (UN KL b))
  eqP (Kleisli l) (Kleisli r) = eqP l r
  showP (Kleisli f) = "Kleisli (" ++ showP f ++ ")"

instance (TestableProfunctor p, Promonad p) => Testable (KLEISLI (p :: Type +-> Type)) where
  type TestOb a = (Ob a, TestOb (UN KL a))
  showOb @(KL a) = "KL " ++ showOb @_ @a
  genOb = genObDef @'[KL Bool, KL (), KL (Maybe Bool)]

instance (EnumAll (f a)) => EnumAll (Prelude f a) where
  enumAll = Prelude <$> enumAll
instance (TestableType (f a)) => TestableType (Prelude f a) where
  gen = fmap Prelude <$> gen
  eqP (Prelude l) (Prelude r) = eqP l r
  showP (Prelude f) = showP f
instance (Function (f a)) => Function (Prelude f a) where
  function = fmap (functionMap Prelude unPrelude) . function

data Pair a = Pair a a
  deriving (Eq, Show, Functor, Generic, Function)
instance (EnumAll a) => EnumAll (Pair a) where
  enumAll = [Pair x y | x <- enumAll, y <- enumAll]
instance (TestableType a) => TestableType (Pair a) where
  gen = liftA2 (liftA2 Pair) gen gen
  eqP (Pair l1 l2) (Pair r1 r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (Pair x y) = "Pair " ++ showP x ++ " " ++ showP y

instance (Functor f, Typeable f, Typeable b, TestOb a, TestOb (f b)) => TestableType (Star (Prelude f) a b) where
  gen = fmap Star <$> gen
  eqP (Star l) (Star r) = eqP l r
  showP (Star f) = showP f

instance (Functor f, Typeable f, Typeable a, TestOb (f a), TestOb b) => TestableType (Costar (Prelude f) a b) where
  gen = optGen (fmap Costar enumAll) -- Somehow using gen @(Prelude f a -> b) causes infinite loops
  eqP (Costar l) (Costar r) = eqP l r
  showP (Costar f) = showP f

instance Promonad (Costar (Prelude Pair)) where
  id = Costar \(Prelude (Pair x _)) -> x
  Costar f . Costar g = Costar (\(Prelude (Pair a b)) -> f (Prelude (Pair (g (Prelude (Pair a b))) (g (Prelude (Pair b b))))))
