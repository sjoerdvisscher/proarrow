{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Props.Strictified (test) where

-- Recorded identity composition is exercised explicitly below.
{- HLINT ignore "Redundant id" -}

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..), testEquality)
import Data.Type.Nat (Nat0, Nat1, Nat2, snat)
import Data.Vec.Lazy (Vec (..))
import Prelude hiding (id, (**), (.))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Proarrow.Category.Instance.Free (FREE (..), emb)
import Proarrow.Category.Instance.FinRel (FINREL (..), FinRel (..))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..), rightUnitor, rightUnitorInv)
import Proarrow.Category.Monoidal.Strictified (Strictified (..), IsList (..), Fold, singleton, withObFold)
import Proarrow.Core (Promonad (..), Ob, Ob')
import Proarrow.Object (ListOf (..))
import Proarrow.Tools.SMC (SYN (..), toSMC, (-<))
import Proarrow.Tools.SMC qualified as SMC
import Proarrow.Testing
  (check, Testable (..), TestableType (..), TestingEqShow (..), TestableProfunctor,
   genSomeDef, invmap, oneElem, oneOfTotal)
import Proarrow.Testing.Laws (testCategory, testMonoidal_, testSymMonoidal_)
import Props.FinRel ()

-- Small relations give exact, inexpensive semantic equality. Include all three
-- list shapes, zero-sized objects, and differently positioned nontrivial wires.
instance Testable [FINREL] where
  showOb @as = show (sizes (sList @as))
    where
      sizes :: ListOf Ob' (xs :: [FINREL]) -> [String]
      sizes Nil = []
      sizes (Cons @x xs) = showOb @FINREL @x : sizes xs
  genSome = genSomeDef
    @'[ '[], '[FR Nat0], '[FR Nat1], '[FR Nat2], '[FR Nat1, FR Nat2],
        '[FR Nat2, FR Nat1], '[FR Nat2, FR Nat2], '[FR Nat1, FR Nat2, FR Nat1]]

sameList :: ListOf Ob' (as :: [FINREL]) -> ListOf Ob' bs -> Maybe (as :~: bs)
sameList Nil Nil = Just Refl
sameList (Cons @(FR a) as) (Cons @(FR b) bs) = do
  Refl <- testEquality (snat @a) (snat @b)
  Refl <- sameList as bs
  pure Refl
sameList _ _ = Nothing

instance (Ob (as :: [FINREL]), Ob bs) => TestingEqShow (Strictified as bs) where
  eqP l r = withObFold @as $ withObFold @bs $ eqP (unStr l) (unStr r)
  showP arrow = withObFold @as $ withObFold @bs $ showP (unStr arrow)

instance (Ob (as :: [FINREL]), Ob bs) => TestableType (Strictified as bs) where
  gen = withObFold @as $ withObFold @bs $
    let arrows = invmap Str unStr (gen @(FinRel (Fold as) (Fold bs)))
    in case sameList (sList @as) (sList @bs) of
      Nothing -> arrows
      Just Refl -> oneOfTotal [oneElem Identity, oneElem (Str id), arrows]

instance TestableProfunctor (Strictified :: [FINREL] -> [FINREL] -> Type)

data Named (a :: Type) (b :: Type) = Named
instance Show (Named a b) where
  show _ = "f"
type K = FREE '[Monoidal] Named
type A = EMB Int :: K

f :: Strictified '[A] '[A]
f = singleton (emb Named)

isIdentity :: Strictified as bs -> Bool
isIdentity Identity = True
isIdentity _ = False

test :: TestTree
test = testGroup "Strictified"
  [ testCategory @[FINREL]
  , testMonoidal_ @[FINREL]
  , testSymMonoidal_ @[FINREL]
  , testProperty "false scalar is retained on either side" $ do
      let scalar = Str (FinRel (0 ::: VNil)) :: Strictified ('[] :: [FINREL]) '[]
          wire = id @Strictified @'[FR Nat2]
          zero = FinRel (0 ::: 0 ::: VNil) :: FinRel (FR Nat2) (FR Nat2)
      check "left scalar lost" (unStr (scalar ** wire) == zero)
      check "right scalar lost" (unStr (wire ** scalar) == zero)
  , testProperty "Identity and Str id have equal interpretations" $ do
      same <- eqP (Identity @'[FR Nat2]) (Str id)
      check "constructor affected equality" same
  , testProperty "composition retains identity information" $
      check "identity lost" (isIdentity ((id . id) :: Strictified '[A] '[A]))
  , testProperty "tensor retains identity information" $
      check "identity lost" (isIdentity ((id @Strictified @'[A]) ** (id @Strictified @'[A])))
  , testProperty "empty tensor identities introduce no unitors" $ do
      check "right identity" (show (unStr (f ** id @Strictified @'[])) == "f")
      check "left identity" (show (unStr (id @Strictified @'[] ** f)) == "f")
  , testProperty "linear SMC binds introduce no base structural arrows" $
      let arrow = unStr $ toSMC @(F '[A]) \x -> SMC.do
            y <- f -< x
            f -< y
      in check "SMC did not lower to composition" (show arrow == show (unStr f . unStr f))
  , testProperty "nonempty identity carries its wire" $
      check "wire lost" (show (unStr (f ** id @Strictified @'[A])) == "f ** id")
  , testProperty "Str view exposes recorded identities" $
      check "identity view" (show (unStr (id @Strictified @'[A])) == "id")
  , testProperty "opaque empty arrows are retained" $
      let scalar = Str (rightUnitor . rightUnitorInv) :: Strictified ('[] :: [K]) '[]
      in check "opaque scalar discarded" (show (unStr (f ** scalar)) /= "f")
  ]
