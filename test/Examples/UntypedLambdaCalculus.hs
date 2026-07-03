{-# LANGUAGE IncoherentInstances #-}

module Examples.UntypedLambdaCalculus where

import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Type.Equality ((:~:) (..))
import Prelude hiding (fst, id, snd, (.))

import Test.Falsify.Generator (Gen, frequency, oneof)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)

import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj, (//))
import Proarrow.Functor (Presheaf)
import Proarrow.Object.Terminal (HasTerminalObject (..))

import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Props (propBinaryProducts_, propCategory, propProfunctor, propTerminalObject)
import Testable
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow
  , mapSome
  , pattern GenNonEmpty
  )

type data CON = Z | S CON

type Sub :: CAT CON
data Sub a b where
  Id :: Sub Z Z
  Comp :: Sub b c -> Sub a b -> Sub a c
  Cons :: Sub a b -> Tm a -> Sub a (S b)
  Wk :: (Ob a) => Sub (S a) a

type Tm a = Tm' a '()
type Tm' :: Presheaf CON
data Tm' a u where
  Vz :: (Ob a) => Tm' (S a) '()
  Vs :: Tm a -> Tm' (S a) '()
  Lam :: Tm (S a) -> Tm' a '()
  App :: Tm a -> Tm a -> Tm' a '()

instance Profunctor Sub where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Comp f g = r \\ f \\ g
  r \\ Cons f _ = r \\ f
  r \\ Wk = r
instance Promonad Sub where
  id @a = case sing @a of
    SZ -> Id
    SS @a' -> lift (obj @a')
  Id . h = h
  f . Id = f
  Comp f g . h = f . (g . h)
  Wk . r = pComp r
    where
      pComp :: (Ob b) => Sub a (S b) -> Sub a b
      pComp (Cons f _) = f
      pComp (Comp g h) = case pComp g of
        Comp Wk x | x == g -> Comp Wk (Comp g h)
        x -> x . h
      pComp s = Comp Wk s
  Cons f t . r = cons (f . r) (lmap r t)
instance CategoryOf CON where
  type (~>) = Sub
  type Ob a = (ConOb a)
instance HasTerminalObject CON where
  type TerminalObject = Z
  terminate @a = case sing @a of
    SZ -> Id
    SS @a' -> terminate @CON @a' . Wk
instance HasBinaryProducts CON where
  type Z && n = n
  type S a && n = S (a && n)
  withObProd @a @b r =
    case sing @a of
      SZ -> r
      SS @a' -> withObProd @CON @a' @b r
  fst @a @b = case sing @a of
    SZ -> terminate
    SS @a' -> let f = fst @CON @a' @b in lift f
  snd @a @b = case sing @a of
    SZ -> id
    SS @a' -> let f = snd @CON @a' @b in f . Wk \\ f
  (&&&) @_ @x l r =
    l // case sing @x of
      SZ -> r
      SS -> cons (Wk . l &&& r) (lmap l Vz)

type SingCon :: CON -> Type
data SingCon a where
  SZ :: SingCon Z
  SS :: (Ob a) => SingCon (S a)

class (a && Z ~ a, (a && b) && c ~ a && (b && c)) => Rules a b c
instance (a && Z ~ a, (a && b) && c ~ a && (b && c)) => Rules a b c

class (forall b c. Rules a b c) => ConOb a where sing :: SingCon a
instance ConOb Z where sing = SZ
instance (Ob a) => ConOb (S a) where sing = SS

instance Profunctor Tm' where
  lmap Id t = t
  lmap (Comp l r) t = lmap r (lmap l t)
  lmap (Cons _ t) Vz = t
  lmap (Cons f _) (Vs t) = lmap f t
  lmap l (Lam t) = Lam (lmap (cons (l . Wk) Vz) t) \\ l
  lmap l (App s t) = App (lmap l s) (lmap l t)
  lmap Wk t = Vs t \\ t

  rmap Unit = id

  r \\ Vz = r
  r \\ Vs t = r \\ t
  r \\ Lam @a t = (case sing @(S a) of SS -> r) \\ t
  r \\ App t _ = r \\ t

lift :: Sub d g -> Sub (S d) (S g)
lift s = Cons (s . Wk) Vz \\ s

($$) :: Tm a -> Tm a -> Tm a
($$) (Lam t) u = lmap (cons id u) t \\ u
($$) t u = App t u

-- simplifies @Cons (Wk . σ) (lmap σ Vz)@ to @σ@
cons :: Sub a b -> Tm a -> Sub a (S b)
cons (Comp Wk s) t = case (countWk s, countVs t) of
  (Just l, Just r) | l == r -> s
  _ -> Cons (Comp Wk s) t
cons s t = Cons s t

countWk :: Sub a b -> Maybe Int
countWk Wk = Just 1
countWk (Comp Wk w) = (+ 1) <$> countWk w
countWk _ = Nothing

countVs :: Tm a -> Maybe Int
countVs Vz = Just 0
countVs (Vs t) = (+ 1) <$> countVs t
countVs _ = Nothing

class b >= a where
  var :: (Ob a) => SingCon a -> Tm (S b)
instance a >= a where
  var _ = Vz
instance (b >= a, Ob b) => S b >= a where
  var _ = lmap Wk (var @b @a sing)

lam :: (Ob a) => (SingCon a -> Tm (S a)) -> Tm a
lam f = Lam (f sing)

y :: Tm Z
y = lam \f -> let fxx = lam \x -> var f $$ (var x $$ var x) in fxx $$ fxx

test :: TestTree
test =
  testGroup
    "Untyped lambda calculus"
    [ propCategory @CON
    , propTerminalObject @CON
    , propBinaryProducts_ @CON
    , testProperty "Tm presheaf" $ propProfunctor @Tm'
    ]

instance Testable CON where
  genSome = frequency [(2, pure (Some @Z)), (1, mapSome S <$> genSome)]
  showOb @a = case sing @a of
    SZ -> "Z"
    SS @b -> "(S " ++ showOb @CON @b ++ ")"
  eqOb @a @b = case (sing @a, sing @b) of
    (SZ, SZ) -> Just Refl
    (SS @a', SS @b') -> case eqOb @CON @a' @b' of
      Just Refl -> Just Refl
      Nothing -> Nothing
    _ -> Nothing

deriving instance Show (Sub a b)
instance Eq (Sub a b) where
  Id == Id = True
  Wk == Wk = True
  Cons a b == Cons c d = a == c && b == d
  Comp @l a b == Comp @r c d =
    a // c // case eqOb @CON @l @r of
      Just Refl -> a == c && b == d
      Nothing -> False
  _ == _ = False

instance (Ob a, Ob b) => TestingEqShow (Sub a b)
instance (Ob a, Ob b) => TestableType (Sub a b) where
  gen = case genDepthSub 8 of
    Just s -> GenNonEmpty s
    Nothing -> GenEmpty $ error $ "Can't generate subst of type Sub " ++ showOb @CON @a ++ " " ++ showOb @CON @b

instance TestableProfunctor Sub

deriving instance Show (Tm a)
instance Eq (Tm a) where
  Vz == Vz = True
  Vs l == Vs r = l == r
  Lam l == Lam r = l == r
  App fl xl == App fr xr = fr == fl && xl == xr
  _ == _ = False
instance (Ob a, Ob b) => TestingEqShow (Tm' a b)
instance (Ob a, Ob b) => TestableType (Tm' a b) where
  gen = case genDepthTm 8 of
    Just t -> GenNonEmpty t
    Nothing -> GenEmpty $ error $ "Can't generate term of type Tm " ++ showOb @CON @a
instance TestableProfunctor Tm'

deriving instance (Show (SingCon a))

genDepthSub :: forall a b. (Ob a, Ob b) => Int -> Maybe (Gen (Sub a b))
genDepthSub 0 = Nothing
genDepthSub d =
  oneof' $
    [ [pure Id | SZ <- [sing @a], SZ <- [sing @b]]
    , [pure Wk | SS @a' <- [sing @a], Just Refl <- [eqOb @CON @a' @b]]
    , [liftA2 cons s t | SS <- [sing @b], Just s <- [genDepthSub (d - 1)], Just t <- [genDepthTm (d - 1)]]
    ]
      ++ [ [liftA2 (.) l r | Just l <- [genDepthSub @m @b (d - 1)], Just r <- [genDepthSub (d - 1)]]
         | Some @m <- [Some @Z, Some @(S Z), Some @(S (S Z)), Some @(S (S (S Z)))]
         ]

genDepthTm :: forall a. (Ob a) => Int -> Maybe (Gen (Tm a))
genDepthTm 0 = Nothing
genDepthTm d =
  oneof' $
    [ [pure Vz | SS <- [sing @a]]
    , [Lam <$> t | Just t <- [genDepthTm (d - 1)]]
    , [liftA2 ($$) l r | Just l <- [genDepthTm (d - 1)], Just r <- [genDepthTm (d - 1)]]
    ]
      ++ [ [liftA2 lmap s t | Just t <- [genDepthTm @b (d - 1)], Just s <- [genDepthSub (d - 1)]]
         | Some @b <- [Some @Z, Some @(S Z), Some @(S (S Z)), Some @(S (S (S Z)))]
         ]

oneof' :: [[Gen a]] -> Maybe (Gen a)
oneof' ls = case concat ls of
  [] -> Nothing
  (g : gs) -> Just (oneof (g :| gs))
