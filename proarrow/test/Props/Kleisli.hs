{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Kleisli where

import Data.Kind (Type)
import Data.Typeable (type (:~:) (..))
import Data.Void (Void)
import GHC.Generics (Generic)
import Test.Falsify.Generator (Function (..))
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (id, (.))

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Prelude (..))
import Proarrow.Profunctor.Instance.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Instance.Star (Star)
import Proarrow.Promonad.Cont (Cont (..))

import Proarrow.Testing
  ( SomeProfunctorElt (..)
  , Testable (..)
  , TestableProfunctor (..)
  , TestableType (..)
  , TestableTypeP
  , TestingEqShow (..)
  , genSomeDef
  , invmap
  )
import Proarrow.Testing.Laws
import Props.Hask ()

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
        "Continuation promonad"
        [ propCategory @(KLEISLI (Cont Void))
        , propTerminalObject @(KLEISLI (Cont Void))
        , propInitialObject @(KLEISLI (Cont Void))
        , propBinaryProducts @(KLEISLI (Cont Void)) (\r -> r)
        , propBinaryCoproducts @(KLEISLI (Cont Void)) (\r -> r)
        , propClosed @(KLEISLI (Cont Void)) (\r -> r) (\r -> r)
        ]
    , testGroup
        "Pair comonad"
        [ propCategory @(KLEISLI (Costar (Prelude Pair)))
        , propTerminalObject @(KLEISLI (Costar (Prelude Pair)))
        , propInitialObject @(KLEISLI (Costar (Prelude Pair)))
        , propBinaryProducts @(KLEISLI (Costar (Prelude Pair))) (\r -> r)
        , propMonoidal @(KLEISLI (Costar (Prelude Pair))) (\r -> r)
        ]
    ]

instance (TestableTypeP p, Promonad p, TestOb a, TestOb b) => TestableType (Kleisli (a :: KLEISLI (p :: Type +-> Type)) b) where
  gen = invmap Kleisli unKleisli (gen @(p (UN KL a) (UN KL b)))
instance (TestingEqShow (p a b), Promonad p) => TestingEqShow (Kleisli (KL a :: KLEISLI (p :: Type +-> Type)) (KL b)) where
  eqP (Kleisli l) (Kleisli r) = eqP l r
  showP (Kleisli f) = "Kleisli (" ++ showP f ++ ")"
instance
  (TestableProfunctor p, TestableTypeP p, Promonad p)
  => TestableProfunctor (Kleisli :: CAT (KLEISLI (p :: Type +-> Type)))
  where
  genProfunctorElt nm = do
    SomeP p <- genProfunctorElt @p nm
    pure $ SomeP (Kleisli p)

instance (TestableProfunctor p, TestableTypeP p, Promonad p) => Testable (KLEISLI (p :: Type +-> Type)) where
  type TestOb a = (Ob a, TestOb (UN KL a))
  showOb @(KL a) = "KL " ++ showOb @_ @a
  eqOb @(KL a) @(KL b) = (\Refl -> Refl) <$> eqOb @Type @a @b
  genSome = genSomeDef @'[KL Bool, KL (), KL (Maybe Bool)]

newtype Pair a = Pair {unPair :: (a, a)}
  deriving (Eq, Show, Functor, Generic)
  deriving anyclass (Function)
instance (TestableType a) => TestableType (Pair a) where
  gen = invmap Pair unPair gen
instance (TestingEqShow a) => TestingEqShow (Pair a) where
  eqP (Pair (l1, l2)) (Pair (r1, r2)) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  showP (Pair (x, y)) = "Pair " ++ showP x ++ " " ++ showP y

instance Promonad (Costar (Prelude Pair)) where
  id = Costar \(Prelude (Pair (x, _))) -> x
  Costar f . Costar g = Costar (\(Prelude (Pair (a, b))) -> f (Prelude (Pair (g (Prelude (Pair (a, b))), g (Prelude (Pair (b, b)))))))

instance (TestOb a, TestOb b) => TestableType (Cont Void a b) where
  gen = invmap Cont runCont gen
instance (TestOb a, TestOb b) => TestingEqShow (Cont Void a b) where
  eqP (Cont l) (Cont r) = eqP l r
  showP (Cont f) = "Cont (" ++ showP f ++ ")"
instance TestableProfunctor (Cont Void)
