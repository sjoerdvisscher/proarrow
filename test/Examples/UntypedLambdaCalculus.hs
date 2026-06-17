-- Following Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics, definition 4
{-# LANGUAGE IncoherentInstances #-}

module Examples.UntypedLambdaCalculus where

import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable)
import Prelude hiding (id, (.))

import Test.Falsify.Generator (Gen, oneof)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)

import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, (//))
import Proarrow.Functor (Presheaf)
import Proarrow.Object.Terminal (HasTerminalObject (..))

import Props (propCategory, propProfunctor, propTerminalObject)
import Testable
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow
  , genSomeDef
  , pattern GenNonEmpty
  )

type data CON = Z | S CON

type Sub :: CAT CON
data Sub a b where
  Id :: (Ob a) => Sub a a
  Comp :: Sub b c -> Sub a b -> Sub a c
  Empty :: (Ob a) => Sub a Z
  Cons :: Sub a b -> Tm a -> Sub a (S b)
  P :: (Ob a) => Sub (S a) a -- tail

type Tm a = Tm' a '()
type Tm' :: Presheaf CON
data Tm' a u where
  Q :: (Ob a) => Tm' (S a) '() -- head
  Subst :: Tm a -> Sub b a -> Tm' b '()
  Lam :: Tm (S a) -> Tm' a '()
  App :: Tm a -> Tm a -> Tm' a '()

instance Profunctor Sub where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Comp f g = r \\ f \\ g
  r \\ Empty = r
  r \\ Cons f _ = r \\ f
  r \\ P = r
instance Promonad Sub where
  id = Id
  Id . h = h
  f . Id = f
  Comp f g . h = f . (g . h)
  Empty . f = Empty \\ f
  P . r = pComp r
    where
      pComp :: (Ob b) => Sub a (S b) -> Sub a b
      pComp (Cons f _) = f
      pComp (Comp g h) = case pComp g of
        Comp P x | x == g -> Comp P (Comp g h)
        x -> x . h
      pComp s = Comp P s
  Cons f t . r = Cons (f . r) (lmap r t)
instance CategoryOf CON where
  type (~>) = Sub
  type Ob a = (ConOb a, Typeable a)
instance HasTerminalObject CON where
  type TerminalObject = Z
  terminate = Empty

type SingCon :: CON -> Type
data SingCon a where
  SZ :: SingCon Z
  SS :: (Ob a) => SingCon (S a)
class ConOb a where sing :: SingCon a
instance ConOb Z where sing = SZ
instance (Ob a) => ConOb (S a) where sing = SS

instance Profunctor Tm' where
  lmap Id t = t
  lmap (Comp l r) t =
    t // case lmap l t of
      x | x == Subst t l -> Subst t (Comp l r)
      x -> lmap r x
  lmap (Cons _ t) Q = t
  lmap l (Lam t) = Lam (lmap (Cons (l . P) Q) t) \\ l
  lmap l (App s t) = App (lmap l s) (lmap l t)
  lmap l (Subst t r) = case r . l of
    x | x == Comp r l -> Subst t x
    x -> lmap x t
  lmap l t = Subst t l \\ t

  rmap Unit = id

  r \\ Q = r
  r \\ Subst _ f = r \\ f
  r \\ Lam @a t = (case sing @(S a) of SS -> r) \\ t
  r \\ App t _ = r \\ t

app :: Tm a -> Tm a -> Tm a
app (Lam t) u = lmap (Cons id u) t \\ u
app t u = App t u

class b >= a where
  var :: (Ob a) => SingCon a -> Tm (S b)
instance a >= a where
  var _ = Q
instance (b >= a, Ob b) => S b >= a where
  var _ = lmap P (var @b @a sing)

lam :: (Ob a) => (SingCon a -> Tm (S a)) -> Tm a
lam f = Lam (f sing)

y :: Tm Z
y = lam \f -> let fxx = lam \x -> var f `app` (var x `app` var x) in fxx `app` fxx

test :: TestTree
test =
  testGroup
    "Untyped lambda calculus"
    [ propCategory @CON
    , propTerminalObject @CON
    , testProperty "Tm presheaf" $ propProfunctor @Tm'
    ]

instance Testable CON where
  genSome = genSomeDef @'[Z, S Z, S (S Z), S (S (S Z))]
  showOb @a = case sing @a of
    SZ -> "Z"
    SS @b -> "(S " ++ showOb @CON @b ++ ")"

deriving instance Show (Sub a b)
instance Eq (Sub a b) where
  Id == Id = True
  Empty == Empty = True
  P == P = True
  Cons a b == Cons c d = a == c && b == d
  Comp @l a b == Comp @r c d = case eqOb @CON @l @r \\ a \\ c of
    Just Refl -> a == c && b == d
    Nothing -> False
  _ == _ = False

instance (Ob a, Ob b) => TestingEqShow (Sub a b)
instance (Ob a, Ob b) => TestableType (Sub a b) where
  gen = case genDepthSub 5 of
    Just s -> GenNonEmpty s
    Nothing -> GenEmpty $ error $ "Can't generate subst of type Sub " ++ showOb @CON @a ++ " " ++ showOb @CON @b

instance TestableProfunctor Sub

deriving instance Show (Tm a)
instance Eq (Tm a) where
  Q == Q = True
  Lam l == Lam r = l == r
  App fl xl == App fr xr = fr == fl && xl == xr
  Subst @l tl sl == Subst @r tr sr = case eqOb @CON @l @r \\ tl \\ tr of
    Just Refl -> tl == tr && sl == sr
    Nothing -> False
  _ == _ = False
instance (Ob a, Ob b) => TestingEqShow (Tm' a b)
instance (Ob a, Ob b) => TestableType (Tm' a b) where
  gen = case genDepthTm 5 of
    Just t -> GenNonEmpty t
    Nothing -> GenEmpty $ error $ "Can't generate term of type Tm " ++ showOb @CON @a
instance TestableProfunctor Tm'

deriving instance (Show (SingCon a))

genDepthSub :: forall a b. (Ob a, Ob b) => Int -> Maybe (Gen (Sub a b))
genDepthSub 0 = Nothing
genDepthSub d =
  oneof' $
    [ [pure Id | Just Refl <- [eqOb @CON @a @b]]
    , [pure Empty | SZ <- [sing @b]]
    , [pure P | SS @a' <- [sing @a], Just Refl <- [eqOb @CON @a' @b]]
    , [liftA2 Cons s t | SS <- [sing @b], Just s <- [genDepthSub (d - 1)], Just t <- [genDepthTm (d - 1)]]
    ]
      ++ [ [liftA2 (.) l r | Just l <- [genDepthSub @m @b (d - 1)], Just r <- [genDepthSub (d - 1)]]
         | Some @m <- [Some @Z, Some @(S Z), Some @(S (S Z)), Some @(S (S (S Z)))]
         ]

genDepthTm :: forall a. (Ob a) => Int -> Maybe (Gen (Tm a))
genDepthTm 0 = Nothing
genDepthTm d =
  oneof' $
    [ [pure Q | SS <- [sing @a]]
    , [Lam <$> t | Just t <- [genDepthTm (d - 1)]]
    , [liftA2 app l r | Just l <- [genDepthTm (d - 1)], Just r <- [genDepthTm (d - 1)]]
    ]
      ++ [ [liftA2 lmap s t | Just t <- [genDepthTm @b (d - 1)], Just s <- [genDepthSub (d - 1)]]
         | Some @b <- [Some @Z, Some @(S Z), Some @(S (S Z)), Some @(S (S (S Z)))]
         ]

oneof' :: [[Gen a]] -> Maybe (Gen a)
oneof' ls = case concat ls of
  [] -> Nothing
  (g : gs) -> Just (oneof (g :| gs))
