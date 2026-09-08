{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.SimplyTypedLambdaCalculus where

import Control.Applicative (Alternative (..))
import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:) (..))
import Prelude hiding (curry, fst, id, snd, (.))

import Test.Falsify.Generator (Function)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)

import Proarrow.Core (CAT, CategoryOf (..), Obj, Profunctor (..), Promonad (..), dimapDefault, obj, (//), type (+->))
import Proarrow.Limit.Terminal (HasTerminalObject (..))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Limit.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  )
import Proarrow.Testing
  ( GenTotal (..)
  , MkSomeList (..)
  , Some (..)
  , SomeProfunctorElt (..)
  , Testable (..)
  , TestableProfunctor (..)
  , TestableType (..)
  , TestingEqShow (..)
  , eqHask
  , genNamed
  , genObSuchThat
  , genSomeDef
  , isGenNonEmpty
  , oneElem
  , oneOfTotal
  )
import Proarrow.Testing.Laws
  ( propBinaryProducts
  , propCategory
  , propClosed
  , propMonoidal
  , propProfunctor
  , propTerminalObject
  )
import Props.Hask ()

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
  one = id
  (**) = (***)

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
  EvalTy K = Bool
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

-- * Testing

--
-- The generators follow the Props.FreeBiCCC recipe: total, type-directed generation via
-- 'GenTotal' ('empty' for uninhabited branches, so nothing is ever discarded), structural
-- recursion wherever a branch shrinks the goal, and a small fixed palette of intermediate
-- objects for the one branch that doesn't ('App'/composition), bounded by fuel. Equality is
-- semantic -- terms and substitutions are compared through 'eval'/'evalSub' -- so the smart
-- normalizing constructors don't have to be confluent for the laws to pass.

-- ** Structural equality and display, needing only 'Ob'

eqTy :: forall (x :: TY) (y :: TY). (Ob x, Ob y) => Maybe (x :~: y)
eqTy = case (ty @x, ty @y) of
  (SK, SK) -> Just Refl
  (SF @a @b, SF @a' @b') -> case (eqTy @a @a', eqTy @b @b') of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  _ -> Nothing

showTy :: forall (a :: TY). (Ob a) => String
showTy = case ty @a of
  SK -> "K"
  SF @a' @b' -> "(" ++ showTy @a' ++ " => " ++ showTy @b' ++ ")"

eqCon :: forall (g :: CON) (h :: CON). (Ob g, Ob h) => Maybe (g :~: h)
eqCon = case (sing @g, sing @h) of
  (SE, SE) -> Just Refl
  (SC @g' @a, SC @h' @b) -> case (eqTy @a @b, eqCon @g' @h') of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
  _ -> Nothing

showCon :: forall (g :: CON). (Ob g) => String
showCon = case sing @g of
  SE -> "E"
  SC @g' @a -> "(" ++ showCon @g' ++ " :> " ++ showTy @a ++ ")"

-- ** Semantic interpretation of substitutions (terms already have 'eval')

evalSub :: Sub g h -> EvalCon g -> EvalCon h
evalSub Empty () = ()
evalSub Wk (g, _) = g
evalSub (Cons s t) g = (evalSub s g, eval t g \\ t)
evalSub (Comp f g) x = evalSub f (evalSub g x)

-- ** Generateability of interpreted values

--
-- 'eqHask' compares interpreted terms by sampling arguments, which needs falsify 'Function'
-- instances at every arrow's /left/ argument. These families thread that requirement through
-- 'TestOb', exactly like @FBCTestOb@ in Props.FreeBiCCC. The palettes below only ever put 'K'
-- on the left of an arrow (and only 'K' entries in contexts), so the vacuous
-- @Function (a -> b)@ instance is never exercised.

type family TyTestOb (a :: TY) :: Constraint where
  TyTestOb K = ()
  TyTestOb (a :=> b) = (Function (EvalTy a), TyTestOb a, TyTestOb b)

type family ConTestOb (g :: CON) :: Constraint where
  ConTestOb E = ()
  ConTestOb (g :> a) = (ConTestOb g, TyTestOb a, Function (EvalTy a))

withEvalTy :: forall (a :: TY) r. (Ob a, TyTestOb a) => ((TestableType (EvalTy a), TestingEqShow (EvalTy a)) => r) -> r
withEvalTy r = case ty @a of
  SK -> r
  SF @x @y -> withEvalTy @x (withEvalTy @y r)

withEvalCon
  :: forall (g :: CON) r. (Ob g, ConTestOb g) => ((TestableType (EvalCon g), TestingEqShow (EvalCon g)) => r) -> r
withEvalCon r = case sing @g of
  SE -> r
  SC @g' @a -> withEvalCon @g' (withEvalTy @a r)

-- ** 'TestOb' is closed under the categorical structure

withTestObProdCON :: forall (a :: CON) b r. (TestOb a, TestOb b) => ((TestOb (a && b)) => r) -> r
withTestObProdCON r = case sing @b of
  SE -> r
  SC @b' -> withTestObProdCON @a @b' r

-- | @'TestOb' ('Exp' d a)@ for an entry type @a@ of a testable context.
withTestObExpArg
  :: forall (d :: CON) a r. (TestOb d, Ob a, TyTestOb a, Function (EvalTy a)) => ((TestOb (Exp d a)) => r) -> r
withTestObExpArg r = case sing @d of
  SE -> r
  SC @d' -> withTestObExpArg @d' @a r

withTestObExpCON :: forall (g :: CON) d r. (TestOb g, TestOb d) => ((TestOb (g ~~> d)) => r) -> r
withTestObExpCON r = case sing @g of
  SE -> r
  SC @g' @a -> withTestObExpArg @d @a (withTestObExpCON @g' @(Exp d a) r)

-- ** Object palettes

type TyPalette = '[K, K :=> K, K :=> (K :=> K)]

tyPalette :: [Some TY]
tyPalette = mkSomeList @TY @TyPalette

type ConPalette = '[E, E :> K, (E :> K) :> K]

conPalette :: [Some CON]
conPalette = mkSomeList @CON @ConPalette

-- ** Total type-directed generators

-- | Generate a term of type @a@ in context @g@. The variable branch recurses structurally on
-- the context and the lambda branch on the type, so both terminate on their own; only 'App'
-- needs an intermediate type (drawn from 'tyPalette') and is bounded by fuel. Uninhabited
-- goals (e.g. @Tm E K@) come out 'empty' instead of looping or discarding.
genTm :: forall (g :: CON) (a :: TY). (Ob g, Ob a) => Int -> GenTotal (Tm g a)
genTm fuel = oneOfTotal [varB, lamB, appB]
  where
    varB = case sing @g of
      SE -> empty
      SC @g' @b ->
        oneOfTotal
          [ case eqTy @b @a of Just Refl -> pure Vz; Nothing -> empty
          , Vs <$> genTm @g' @a fuel
          ]
    lamB = case ty @a of
      SK -> empty
      SF @a1 @a2 -> Lam <$> genTm @(g :> a1) @a2 fuel
    appB
      | fuel <= 0 = empty
      | otherwise =
          oneOfTotal
            [ App <$> genTm @g @(c :=> a) (fuel - 1) <*> genTm @g @c (fuel - 1)
            | Some @c <- tyPalette
            ]

-- | Generate a substitution, type-directed on both contexts: identity and weakening when the
-- shapes allow it, 'terminate' into the empty context, 'cons' peeling the target context (which
-- terminates structurally), and fuel-bounded composition through 'conPalette'.
genSub :: forall (g :: CON) (h :: CON). (Ob g, Ob h) => Int -> GenTotal (Sub g h)
genSub fuel = oneOfTotal [idB, termB, wkB, consB, compB]
  where
    idB = case eqCon @g @h of Just Refl -> pure id; Nothing -> empty
    termB = case sing @h of SE -> pure terminate; SC -> empty
    wkB = case sing @g of
      SE -> empty
      SC @g' -> (. Wk) <$> genSub @g' @h fuel
    consB = case sing @h of
      SE -> empty
      SC @h' @a -> cons <$> genSub @g @h' fuel <*> genTm @g @a fuel
    compB
      | fuel <= 0 = empty
      | otherwise =
          oneOfTotal
            [ (.) <$> genSub @m @h (fuel - 1) <*> genSub @g @m (fuel - 1)
            | Some @m <- conPalette
            ]

-- ** Testable instances

instance Testable TY where
  type TestOb a = (IsTy a, TyTestOb a)
  showOb @a = showTy @a
  eqOb = eqTy
  genSome = genSomeDef @TyPalette

deriving instance Show (Ty a b)
deriving instance Eq (Ty a b)
instance (Ob a, Ob b) => TestingEqShow (Ty a b)
instance (Ob a, Ob b) => TestableType (Ty a b) where
  gen = case eqTy @a @b of
    Just Refl -> oneElem (ty @a)
    Nothing -> GenEmpty (error "gen @Ty")
instance TestableProfunctor Ty

instance Testable CON where
  type TestOb g = (ConOb g, ConTestOb g)
  showOb @g = showCon @g
  eqOb = eqCon
  genSome = genSomeDef @ConPalette

deriving instance Show (Sub a b)

-- | Structural equality, used by the normalizing smart constructors ('cons', 'pComp') -- the
-- test suite compares substitutions semantically instead, see 'TestingEqShow'.
instance Eq (Sub a b) where
  Empty == Empty = True
  Wk == Wk = True
  Cons a b == Cons c d = a == c && b == d
  Comp @l a b == Comp @r c d =
    a // c // case eqCon @l @r of
      Just Refl -> a == c && b == d
      Nothing -> False
  _ == _ = False

instance (Ob a, ConTestOb a, Ob b, ConTestOb b) => TestingEqShow (Sub a b) where
  eqP l r = withEvalCon @a (withEvalCon @b (eqHask (evalSub l) (evalSub r)))
  showP = show
instance (Ob a, ConTestOb a, Ob b, ConTestOb b) => TestableType (Sub a b) where
  gen = genSub @a @b 3
instance TestableProfunctor Sub where
  genProfunctorElt nm = do
    Some @g <- genObSuchThat @CON \(Some @g') -> any (\(Some @h') -> isGenNonEmpty @(Sub g' h')) conPalette
    Some @h <- genObSuchThat @CON \(Some @h') -> isGenNonEmpty @(Sub g h')
    s <- genNamed @(Sub g h) nm
    pure (SomeP s)

deriving instance Show (Tm g a)

-- | Structural equality, only used by @Eq Sub@ above.
instance Eq (Tm g a) where
  Vz == Vz = True
  Lam l == Lam r = l == r
  App @al fl xl == App @ar fr xr =
    xl // xr // case eqTy @al @ar of
      Just Refl -> xl == xr && fl == fr
      Nothing -> False
  Vs tl == Vs tr = tl == tr
  _ == _ = False

instance (Ob g, ConTestOb g, Ob a, TyTestOb a) => TestingEqShow (Tm g a) where
  eqP l r = withEvalCon @g (withEvalTy @a (eqHask (eval l) (eval r)))
  showP = show
instance (Ob g, ConTestOb g, Ob a, TyTestOb a) => TestableType (Tm g a) where
  gen = genTm @g @a 3
instance TestableProfunctor Tm where
  genProfunctorElt nm = do
    Some @g <- genObSuchThat @CON \(Some @g') -> any (\(Some @a') -> isGenNonEmpty @(Tm g' a')) tyPalette
    Some @a <- genObSuchThat @TY \(Some @a') -> isGenNonEmpty @(Tm g a')
    t <- genNamed @(Tm g a) nm
    pure (SomeP t)

test :: TestTree
test =
  testGroup
    "Simply typed lambda calculus"
    [ propCategory @CON
    , propTerminalObject @CON
    , propBinaryProducts @CON (\ @a @b r -> withTestObProdCON @a @b r)
    , propMonoidal @CON (\ @a @b r -> withTestObProdCON @a @b r)
    , propClosed @CON (\ @a @b r -> withTestObProdCON @a @b r) (\ @a @b r -> withTestObExpCON @a @b r)
    , testProperty "Tm profunctor" $ propProfunctor @Tm
    ]
