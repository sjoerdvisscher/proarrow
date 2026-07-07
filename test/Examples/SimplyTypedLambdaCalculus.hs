{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.SimplyTypedLambdaCalculus where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Prelude hiding (curry, fst, id, snd, (.))

import Test.Falsify.Generator (Gen, frequency)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)

import Proarrow.Core (CAT, CategoryOf (..), Obj, Profunctor (..), Promonad (..), dimapDefault, obj, (//), type (+->))
import Proarrow.Object.Terminal (HasTerminalObject (..))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  )
import Proarrow.Object.Exponential (Closed (..))
import Props (propCategory, propProfunctor, propTerminalObject)
import Testable
  ( GenTotal (..)
  , Some (..)
  , SomeProfunctorElt (..)
  , Testable (..)
  , TestableProfunctor (..)
  , TestableType (..)
  , TestingEqShow
  , genWithNamed
  , one
  , someP
  , pattern GenNonEmpty
  )

type data TY = K | TY :=> TY

class IsTy (a :: TY) where ty :: Obj a
instance IsTy K where ty = SK
instance (IsTy a, IsTy b) => IsTy (a :=> b) where ty = SF

type Ty :: CAT TY
data Ty g h where
  SK :: Ty K K
  SF :: (Ob a, Ob b) => Ty (a :=> b) (a :=> b)
instance Profunctor Ty where
  dimap = dimapDefault
  r \\ SK = r
  r \\ SF = r
instance Promonad Ty where
  id = ty
  SK . SK = SK
  SF . SF = SF
instance CategoryOf TY where
  type (~>) = Ty
  type Ob a = (IsTy a)

type data CON = E | CON :> TY

type Sub :: CAT CON
data Sub g h where
  Comp :: Sub h j -> Sub g h -> Sub g j
  Empty :: Sub E E
  Cons :: Sub g h -> Tm g a -> Sub g (h :> a)
  Wk :: (Ob a, Ob g) => Sub (g :> a) g

type Tm :: TY +-> CON
data Tm g a where
  Vz :: (Ob a, Ob g) => Tm (g :> a) a
  Vs :: (Ob b) => Tm g a -> Tm (g :> b) a
  Lam :: (Ob g, Ob a) => Tm (g :> a) b -> Tm g (a :=> b)
  App :: forall a b g. (Ob b) => Tm g (a :=> b) -> Tm g a -> Tm g b

instance Profunctor Sub where
  dimap = dimapDefault
  r \\ Comp f g = r \\ f \\ g
  r \\ Empty = r
  r \\ Cons f t = r \\ f \\ t
  r \\ Wk = r
instance Promonad Sub where
  id @a = case sing @a of
    SE -> Empty
    SC @g' -> Cons (obj @g' . Wk) Vz
  Comp f g . h = f . (g . h)
  Empty . f = f
  Wk @a . r = pComp r
    where
      pComp :: (Ob g) => Sub h (g :> a) -> Sub h g
      pComp (Cons f _) = f
      pComp (Comp g h) = case pComp g of
        c | c == Comp Wk g -> Comp Wk (Comp g h)
        x -> x . h
      pComp s = Comp Wk s
  Cons f t . r = cons (f . r) (lmap r t)
instance CategoryOf CON where
  type (~>) = Sub
  type Ob a = (ConOb a)
instance HasTerminalObject CON where
  type TerminalObject = E
  terminate @a = case sing @a of
    SE -> Empty
    SC @a' -> terminate @CON @a' . Wk

instance HasBinaryProducts CON where
  type n && E = n
  type n && (g :> a) = (n && g) :> a

  withObProd @a @b r =
    case sing @b of
      SE -> r
      SC @b' -> withObProd @CON @a @b' r
  fst @a @b = case sing @b of
    SE -> obj @a
    SC @b' -> let f = fst @CON @a @b' in f . Wk \\ f
  snd @a @b = case sing @b of
    SE -> terminate
    SC @b' -> let f = snd @CON @a @b' in lift f
  (&&&) @_ @_ @y l r =
    r // case sing @y of
      SE -> l
      SC -> cons (l &&& Comp Wk r) (lmap r Vz)

instance MonoidalProfunctor Sub where
  par0 = id
  par = (***)

instance Monoidal CON where
  type a ** b = a && b
  type Unit = TerminalObject
  withOb2 @a @b = withObProd @_ @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @a @b @c = associatorProd @a @b @c
  associatorInv @a @b @c = associatorProdInv @a @b @c

type family Exp (g :: CON) (a :: TY) :: CON where
  Exp E _ = E
  Exp (g :> b) a = Exp g a :> (a :=> b)

withObExpSub :: forall g a r. (Ob g, Ob a) => ((Ob (Exp g a)) => r) -> r
withObExpSub r = case sing @g of
  SE -> r
  SC @g' -> withObExpSub @g' @a r

currySub :: forall a d g. (Ob g, Ob a) => Sub (g :> a) d -> Sub g (Exp d a)
currySub s =
  s // case sing @d of
    SE -> terminate
    SC -> case uncons s of (s1, t) -> cons (currySub s1) (Lam t)

uncurrySub :: forall a d g. (Ob d, Ob a) => Sub g (Exp d a) -> Sub (g :> a) d
uncurrySub s =
  s // case sing @d of
    SE -> terminate
    SC @g' -> withObExpSub @g' @a $ case uncons s of (s', t) -> cons (uncurrySub s') (App (Vs t) Vz)

instance Closed CON where
  type E ~~> d = d
  type (g :> a) ~~> d = g ~~> Exp d a
  withObExp @g @d r = case sing @g of
    SE -> r
    SC @g' @a -> withObExpSub @d @a $ withObExp @CON @g' @(Exp d a) r
  curry @d @g f =
    f // case sing @g of
      SE -> f
      SC @g' -> withObProd @CON @d @g' (curry @CON @d @g' (currySub f))
  apply @d @g = case sing @d of
    SE -> id
    SC @d' @a -> withObExpSub @g @a $ uncurrySub (apply @CON @d' @(Exp g a))

class (E && a ~ a, (c && b) && a ~ c && (b && a)) => Rules a b c
instance (E && a ~ a, (c && b) && a ~ c && (b && a)) => Rules a b c

type SingCon :: CON -> Type
data SingCon g where
  SE :: SingCon E
  SC :: (Ob g, Ob a) => SingCon (g :> a)
class (forall b c. Rules g b c) => ConOb g where sing :: SingCon g
instance ConOb E where sing = SE
instance (Ob g, Ob a) => ConOb (g :> a) where sing = SC

instance Profunctor Tm where
  lmap (Comp l r) t = lmap r (lmap l t)
  lmap (Cons _ t) Vz = t
  lmap (Cons f _) (Vs t) = lmap f t
  lmap l (Lam t) = Lam (lmap (cons (l . Wk) Vz) t) \\ l
  lmap l (App s t) = App (lmap l s) (lmap l t)
  lmap Wk t = Vs t

  rmap SK = id
  rmap SF = id

  r \\ Vz = r
  r \\ Vs f = r \\ f
  r \\ Lam t = r \\ t
  r \\ App t _ = r \\ t

uncons :: forall g d a. (Ob d, Ob a) => Sub g (d :> a) -> (Sub g d, Tm g a)
uncons (Cons s t) = (s, t)
uncons (Comp l r) = case uncons l of
  (s, t) -> (s . r, lmap r t)
uncons Wk = (Wk . Wk, Vs Vz)

lift :: (Ob a) => Sub d g -> Sub (d :> a) (g :> a)
lift s = Cons (s . Wk) Vz \\ s

weakenR :: (Ob a) => Sub d g -> Sub (d && a) (g && a)
weakenR @a f =
  f // case sing @a of
    SE -> f
    SC @a' @x -> lift @x (weakenR @a' f)

-- simplifies @Cons (Wk . σ) (lmap σ Vz)@ to @σ@
cons :: Sub d g -> Tm d a -> Sub d (g :> a)
cons (Comp Wk s) t = case (countWk s, countVs t) of
  (Just l, Just r) | l == r -> case uncons s of (s', _) -> Cons s' t
  _ -> s // Cons (Comp Wk s) t
cons s t = Cons s t

countWk :: Sub a b -> Maybe Int
countWk Wk = Just 1
countWk (Comp Wk w) = (+ 1) <$> countWk w
countWk _ = Nothing

countVs :: Tm g a -> Maybe Int
countVs Vz = Just 0
countVs (Vs t) = (+ 1) <$> countVs t
countVs _ = Nothing

app :: (Ob b) => Tm g (a :=> b) -> Tm g a -> Tm g b
app (Lam t) u = lmap (cons id u) t \\ u
app t u = App t u

lam :: (Ob g, Ob a) => (SingCon g -> Tm (g :> a) b) -> Tm g (a :=> b)
lam f = Lam (f sing)

type family EvalTy (a :: TY) :: Type where
  EvalTy K = Int
  EvalTy (a :=> b) = EvalTy a -> EvalTy b

type family EvalCon (g :: CON) :: Type where
  EvalCon E = ()
  EvalCon (g :> a) = (EvalCon g, EvalTy a)

eval :: (Ob a) => Tm g a -> EvalCon g -> EvalTy a
eval Vz (_, x) = x
eval (Vs f) (g, _) = eval f g
eval (Lam f) g = \x -> eval f (g, x) \\ f
eval (App t u) g = eval t g (eval u g) \\ u

type Nat a = (a :=> a) :=> (a :=> a)

-- \f z -> z
nat0 :: (Ob a) => Tm E (Nat a)
nat0 = Lam (Lam Vz)

-- \f z -> f z
nat1 :: (Ob a) => Tm E (Nat a)
nat1 = Lam (Lam (App (Vs Vz) Vz))

-- \n f z -> f (n f z)
succ :: (Ob a) => Tm E (Nat a :=> Nat a)
succ = Lam (Lam (Lam (App (Vs Vz) (App (App (Vs (Vs Vz)) (Vs Vz)) Vz))))

-- class d >= g where
--   var :: (Ob g) => SingCon g -> Tm (S a d) b
-- instance g >= g where
--   var _ = Vz
-- instance (d >= g, Ob d) => S a d >= g where
--   var _ = Vs (var @d @g sing)

test :: TestTree
test =
  testGroup
    "Simply typed lambda calculus"
    [ propCategory @CON
    , propTerminalObject @CON
    , testProperty "Tm profunctor" $ propProfunctor @Tm
    ]

instance Testable TY where
  genSome =
    frequency
      [ (2, pure (Some @K))
      ,
        ( 1
        , do
            Some @a <- genSome
            Some @b <- genSome
            pure (Some @(a :=> b))
        )
      ]
  showOb @a = case ty @a of
    SK -> "K"
    SF @a' @b' -> "(" ++ showOb @TY @a' ++ " => " ++ showOb @TY @b' ++ ")"
  eqOb @x @y = case (ty @x, ty @y) of
    (SK, SK) -> Just Refl
    (SF @a @b, SF @a' @b') -> case (eqOb @TY @a @a', eqOb @TY @b @b') of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
    _ -> Nothing

deriving instance Show (Ty a b)
deriving instance Eq (Ty a b)
instance (Ob a, Ob b) => TestingEqShow (Ty a b)
instance (Ob a, Ob b) => TestableType (Ty a b) where
  gen = case eqOb @TY @a @b of
    Just Refl -> one (ty @a)
    Nothing -> GenEmpty $ error "gen @Ty"
instance TestableProfunctor Ty

instance Testable CON where
  genSome =
    frequency
      [ (2, pure (Some @E))
      ,
        ( 1
        , do
            Some @t <- genSome
            Some @c <- genSome
            pure (Some @(c :> t))
        )
      ]
  showOb @a = case sing @a of
    SE -> "E"
    SC @g @b -> "(" ++ showOb @CON @g ++ " :> " ++ showOb @TY @b ++ ")"
  eqOb @a @b = case (sing @a, sing @b) of
    (SE, SE) -> Just Refl
    (SC @g @a', SC @g' @b') -> case (eqOb @TY @a' @b', eqOb @CON @g @g') of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
    _ -> Nothing

deriving instance Show (Sub a b)
instance Eq (Sub a b) where
  Empty == Empty = True
  Wk == Wk = True
  Cons a b == Cons c d = a == c && b == d
  Comp @l a b == Comp @r c d =
    a // c // case eqOb @CON @l @r of
      Just Refl -> a == c && b == d
      Nothing -> False
  _ == _ = False
instance (Ob a, Ob b) => TestingEqShow (Sub a b)
instance (Ob a, Ob b) => TestableType (Sub a b) where
  gen = GenNonEmpty $ do
    -- Some @c <- genSome
    frequency $
      concat @[] $
        [ [(5, pure Empty) | SE <- [sing @a], SE <- [sing @b]]
        , [(5, pure Wk) | SC @a' <- [sing @a], Just Refl <- [eqOb @CON @a' @b]]
        , [(1, liftA2 cons s t) | SC <- [sing @b], GenNonEmpty s <- [gen], GenNonEmpty t <- [gen]]
        -- , [(2, liftA2 (.) l r) | GenNonEmpty l <- [gen], GenNonEmpty r <- [gen @(Sub a a)]]
        -- , [(2, liftA2 (.) l r) | GenNonEmpty l <- [gen], GenNonEmpty r <- [gen @(Sub a b)]]
        -- , [(1, liftA2 (.) l r) | GenNonEmpty l <- [gen], GenNonEmpty r <- [gen @(Sub a c)]]
        ]

instance TestableProfunctor Sub

deriving instance Show (Tm g a)
instance Eq (Tm g a) where
  Vz == Vz = True
  Lam l == Lam r = l == r
  App @al fl xl == App @ar fr xr =
    xl // xr // case eqOb @TY @al @ar of
      Just Refl -> xl == xr && fl == fr
      Nothing -> False
  Vs tl == Vs tr = tl == tr
  _ == _ = False

instance (Ob a, Ob g) => TestingEqShow (Tm g a)
instance (Ob a, Ob g) => TestableType (Tm g a) where
  gen = GenNonEmpty $ do
    Some @c <- genSome
    frequency $
      concat @[] $
        [ [(4, pure Vz) | SC @_ @a' <- [sing @g], Just Refl <- [eqOb @TY @a' @a]]
        , [(1, Vs <$> t) | SC <- [sing @g], GenNonEmpty t <- [gen]]
        , [(1, Lam <$> t) | SF <- [ty @a], GenNonEmpty t <- [gen]]
        , [(1, liftA2 App l r) | GenNonEmpty l <- [gen @(Tm g (c :=> a))], GenNonEmpty r <- [gen]]
        ]

instance TestableProfunctor Tm where
  genProfunctorElt nm = genWithNamed nm (Just . show) genTm

genTm :: Gen (SomeProfunctorElt Tm)
genTm =
  frequency
    [ (2, do Some @a <- genSome; Some @g <- genSome; pure $ someP (Vz @a @g))
    , (1, do SomeP t <- genTm; Some @b <- genSome; pure $ SomeP (Vs @b t))
    ,
      ( 1
      , do
          SomeP @g t <- genTm
          case sing @g of
            SE -> do Some @b <- genSome; pure $ SomeP (Lam (Vs @b t))
            SC -> pure $ SomeP (Lam t)
      )
      -- ,
      --   ( 1
      --   , let go :: Gen (SomeProfunctorElt Tm) = do
      --           SomeP @g' l <- genTm
      --           SomeP @g @a r <- genTm
      --           case eqOb @CON @(g :> a) @g' of
      --             Just Refl -> pure $ SomeP (App (Lam l) r)
      --             Nothing -> go
      --     in go
      --   )
    ]
