{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Kleisli where

import Data.Kind (Type)
import Data.Typeable (Typeable)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (id)

import Proarrow.Category.Instance.Free (Show2)
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Prelude (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Star (Star (..))

import Props
import Props.Hask (EnumAll (..))
import Testable (TestOb', Testable (..), TestableProfunctor (..), genObDef)

test :: TestTree
test =
  testGroup
    "Kleisli"
    [ testGroup
        "Maybe monad"
        [ propCategory @(KLEISLI (Star (Prelude Maybe)))
        , propInitialObject @(KLEISLI (Star (Prelude Maybe)))
        , propBinaryCoproducts @(KLEISLI (Star (Prelude Maybe))) (\r -> r)
        ]
    , testGroup
        "Pair comonad"
        [ propCategory @(KLEISLI (Costar (Prelude Pair)))
        , propTerminalObject @(KLEISLI (Costar (Prelude Pair)))
        , propInitialObject @(KLEISLI (Costar (Prelude Pair)))
        ]
    ]

instance (TestOb a, TestOb b, Show2 p) => Show (Kleisli a (b :: KLEISLI p)) where
  show (Kleisli f) = show f

instance (TestableProfunctor p, Promonad p) => TestableProfunctor (Kleisli :: CAT (KLEISLI (p :: Type +-> Type))) where
  genP = Kleisli <$> genP
  eqP (Kleisli l) (Kleisli r) = eqP l r
  showP (Kleisli f) = showP f

instance (TestableProfunctor p, Promonad p) => Testable (KLEISLI (p :: Type +-> Type)) where
  type TestOb a = (Ob a, TestOb (UN KL a))
  showOb @(KL a) = showOb @_ @a
  genOb = genObDef @'[KL Bool, KL (), KL (Maybe Bool)]

instance (EnumAll (f a)) => EnumAll (Prelude f a) where
  enumAll = Prelude <$> enumAll

data Pair a = Pair a a
  deriving (Eq, Show, Functor)
instance (EnumAll a) => EnumAll (Pair a) where
  enumAll = [Pair x y | x <- enumAll, y <- enumAll]

instance (forall a. (TestOb a) => TestOb' (f a), Functor f, Typeable f) => TestableProfunctor (Star (Prelude f)) where
  genP = Star <$> genP
  eqP (Star l) (Star r) = eqP l r
  showP (Star f) = showP f

instance (forall a. (TestOb a) => TestOb' (f a), Functor f, Typeable f) => TestableProfunctor (Costar (Prelude f)) where
  genP = Costar <$> genP
  eqP (Costar l) (Costar r) = eqP l r
  showP (Costar f) = showP f

instance Promonad (Costar (Prelude Pair)) where
  id = Costar \(Prelude (Pair x _)) -> x
  Costar f . Costar g = Costar (\(Prelude (Pair a b)) -> f (Prelude (Pair (g (Prelude (Pair a b))) (g (Prelude (Pair b b))))))
