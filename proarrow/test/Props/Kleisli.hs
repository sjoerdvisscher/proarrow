{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Kleisli where

import Data.Kind (Type)
import Data.Typeable (type (:~:) (..))
import Data.Void (Void)
import GHC.Generics (Generic)
import Test.Falsify.Generator (Function (..))
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Thin (Holds, Objects)
import Proarrow.Category.Enriched.Thin.Composition (Closure)
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans)
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
        [ testCategory @(KLEISLI (Star (Prelude Maybe)))
        , testInitialObject @(KLEISLI (Star (Prelude Maybe)))
        , testMonoidal @(KLEISLI (Star (Prelude Maybe))) (\r -> r)
        , testMonoidalHom @(KLEISLI (Star (Prelude Maybe))) (\r -> r)
        , testSymMonoidal @(KLEISLI (Star (Prelude Maybe))) (\r -> r)
        , testCopyDiscard @(KLEISLI (Star (Prelude Maybe))) (\r -> r) (\r -> r)
        , testBinaryCoproducts @(KLEISLI (Star (Prelude Maybe))) (\r -> r)
        ]
    , testGroup
        "Continuation promonad"
        [ testCategory @(KLEISLI (Cont Void))
        , -- No terminal object, products or 'testCartesian' here: those lift to the co-Kleisli
          -- category of a 'Comonad', and @'Cont' r@ is a monad, not a comonad. They did hold at
          -- @'Cont' 'Void'@, but only because every hom-set in this group is a singleton (see the
          -- note below), not for any reason that generalises.
          testInitialObject @(KLEISLI (Cont Void))
        , testBinaryCoproducts @(KLEISLI (Cont Void)) (\r -> r)
        , testClosed @(KLEISLI (Cont Void)) (\r -> r) (\r -> r)
        , -- Note this group is close to vacuous: @Cont Void a b@ is @(b -> Void) -> (a -> Void)@,
          -- and every object in the palette is inhabited, so every hom-set here is a singleton and
          -- every law holds trivially. A non-empty answer type would make it meaningful, but the
          -- generator for @(b -> r) -> (a -> r)@ does not currently support one.
          testMonoidalHom @(KLEISLI (Cont Void)) (\r -> r)
        ]
    , testGroup
        "Pair comonad"
        [ testCategory @(KLEISLI (Costar (Prelude Pair)))
        , testTerminalObject @(KLEISLI (Costar (Prelude Pair)))
        , -- No initial object: that lifts for a 'Monad', and @'Costar' f@ is a comonad. It did
          -- hold here because @'Pair' 'Void'@ is itself empty, which is a fact about 'Pair' rather
          -- than about comonads.
          testBinaryProducts @(KLEISLI (Costar (Prelude Pair))) (\r -> r)
        , testCartesian @(KLEISLI (Costar (Prelude Pair))) (\r -> r) (\r -> r)
        , testMonoidal @(KLEISLI (Costar (Prelude Pair))) (\r -> r)
        , testMonoidalHom @(KLEISLI (Costar (Prelude Pair))) (\r -> r)
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

-- * The Kleisli category of a decidable promonad is enumerable

-- | Its objects are those of the base, numbered the same way.
objectsKleisli :: Objects (KLEISLI Booleans) :~: '[KL FLS, KL TRU]
objectsKleisli = Refl

-- | So it can be searched: the closure of the walking arrow's own hom still only goes upwards.
-- This only typechecks because the Kleisli category is enumerable.
kleisliReaches :: Holds (Closure (Kleisli :: CAT (KLEISLI Booleans))) (KL FLS) (KL TRU) :~: TRU
kleisliReaches = Refl

kleisliNoWayBack :: Holds (Closure (Kleisli :: CAT (KLEISLI Booleans))) (KL TRU) (KL FLS) :~: FLS
kleisliNoWayBack = Refl
