{-# LANGUAGE AllowAmbiguousTypes #-}

{- HLINT ignore "Redundant $" -}

-- | A small HOAS (higher-order abstract syntax) front end for building morphisms in any
-- 'BiCCC', compiling through "Proarrow.Category.Instance.FreeBiCCC"'s free bicartesian closed
-- category rather than a bespoke one. A 'Free' term tracks its free variables via a context
-- list, the way a well-scoped lambda calculus does; 'lam' binds an ordinary Haskell-level
-- variable that 'Cast' automatically "weakens" across nested lambdas so inner lambdas can still
-- refer to outer ones. 'toCCC' interprets a closed term (no free variables) into an actual
-- morphism of the target category.
module Proarrow.Tools.CCC
  ( toCCC
  , lam
  , ($)
  , lift
  , pattern (:&)
  , either
  , lft
  , rgt
  , Free
  , FBC (..)
  , type F
  , injectRight
  , swapProduct
  , applyPair
  , curryPair
  , flipCurried3
  , swapSum
  , caseEither
  ) where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Instance.FreeBiCCC (FBC (..), KnownFBCOb, Lower, Term (Emb), fbcOb, interp)
import Proarrow.Category.Monoidal.Closed (BiCCC, Closed (..), lower)
import Proarrow.Category.Monoidal.Distributive (distLProd)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts ((|||)), type (||))
import Proarrow.Colimit.BinaryCoproduct qualified as BC
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object (Obj)
import Proarrow.Profunctor.Instance.Identity (Id (..))

infixr 0 $

-- | The generating profunctor for the free BiCCC below: @k@'s own hom-sets, i.e. 'Id'
-- (rather than @(~>)@ itself, which — being an unsaturated type family application — isn't
-- allowed as a type index wherever 'FBC' is pattern-matched on below, in 'Mul').
type Ctx k = [FBC (Id :: CAT k)]

-- | A short alias for embedding a base-category object, so type applications built from it read
-- closer to the target signature's own use of '&&'\/'||'\/'~~>' (e.g. @(F a ~~> F b) && F a@
-- instead of @'PROD' ('EXPO' ('OBJ' a) ('OBJ' b)) ('OBJ' a)@) — those are already the very same
-- operators 'FBC' gets from 'HasBinaryProducts'\/'HasBinaryCoproducts'\/'Closed', just spelled
-- out as their underlying constructors.
type F a = OBJ a

-- | The context product: @'Mul' i@ is the single object standing in for "all the bound
-- variables in @i@", right fold with the most-recently-bound variable last — the mirror image
-- of "Proarrow.Category.Monoidal.Strictified"'s @Fold@ (which puts its head /leftmost/), needed
-- here since 'curry'\/'fst'\/'snd' expect the thing being abstracted over on the /right/ of the
-- product, not the left, so @Fold@ itself can't be reused for this.
type family Mul (i :: Ctx k) :: FBC (Id :: CAT k) where
  Mul '[] = UNIT
  Mul (a ': as) = Mul as && a

-- | A term with free variables @i@ (innermost\/most-recently-bound first) and result type
-- @a@ — literally a morphism from the context product to @a@ in the free BiCCC. A newtype
-- (rather than a bare type synonym for @'Term' ('Mul' i) a@) so that @i@ is recoverable from
-- a 'Free' term's type: 'Mul' is many-to-one at the type-family level as far as GHC's
-- injectivity checker is concerned (even though it's mathematically injective here), which
-- would otherwise leave @i@ ambiguous wherever it has to be inferred rather than given
-- explicitly (e.g. picking which context a HOAS variable reference in 'lam' denotes).
newtype Free (i :: Ctx k) (a :: FBC (Id :: CAT k)) = MkFree {unFree :: Term (Mul i) a}

type KnownCtx :: forall {k}. Ctx k -> Constraint
class (BiCCC k) => KnownCtx (i :: Ctx k) where
  ctxOb :: Obj (Mul i)
  pushOb :: forall a. (KnownFBCOb a) => Obj (Mul (a ': i))

instance (BiCCC k) => KnownCtx ('[] :: Ctx k) where
  ctxOb = id
  pushOb @a = withObProd @(FBC (Id :: CAT k)) @UNIT @a id \\ fbcOb @a

instance (KnownCtx i, KnownFBCOb (b :: FBC (Id :: CAT k))) => KnownCtx (b ': i) where
  ctxOb = pushOb @i @b
  pushOb @a = withObProd @(FBC (Id :: CAT k)) @(Mul (b ': i)) @a id \\ ctxOb @(b ': i) \\ fbcOb @a

-- | The most-recently-bound variable.
headT :: forall {k} a i. (KnownCtx (i :: Ctx k), KnownFBCOb (a :: FBC (Id :: CAT k))) => Free (a ': i) a
headT = MkFree (snd @(FBC (Id :: CAT k)) @(Mul i) @a \\ ctxOb @i \\ fbcOb @a)

-- | Weaken a term by one more bound variable it doesn't use.
tailT :: forall {k} a i b. (KnownCtx (i :: Ctx k), KnownFBCOb (a :: FBC (Id :: CAT k))) => Free i b -> Free (a ': i) b
tailT (MkFree f) = MkFree (f . fst @(FBC (Id :: CAT k)) @(Mul i) @a \\ ctxOb @i \\ fbcOb @a)

-- | @'Cast' i j@ holds when context @i@ is context @j@ with zero or more extra variables
-- pushed on top, letting a term built for @j@ be used anywhere \"deeper\" than @j@.
type Cast :: forall {k}. Ctx k -> Ctx k -> Constraint
class Cast (i :: Ctx k) (j :: Ctx k) where
  cast :: (KnownFBCOb (a :: FBC (Id :: CAT k))) => Free j a -> Free i a

instance Cast i i where
  cast f = f

instance
  {-# OVERLAPPABLE #-}
  (Cast i j, KnownCtx (i :: Ctx k), KnownFBCOb (b :: FBC (Id :: CAT k)), (b ': i) ~ i')
  => Cast i' j
  where
  cast f = tailT (cast f)

-- | Bind a variable, HOAS-style: the function argument stands for the newly bound variable,
-- usable (via 'Cast') in the body of this 'lam' and any 'lam' nested inside it.
lam
  :: forall {k} a b i
   . (KnownCtx (i :: Ctx k), KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b)
  => ((forall (x :: Ctx k). (Cast x (a ': i)) => Free x a) -> Free (a ': i) b)
  -> Free i (EXPO a b)
lam f = MkFree (curry @(FBC (Id :: CAT k)) @(Mul i) @a @b (unFree (f xa)) \\ ctxOb @i \\ fbcOb @a)
  where
    xa :: forall (x :: Ctx k). (Cast x (a ': i)) => Free x a
    xa = cast (headT @a @i)

-- | Function application.
($)
  :: forall {k} a b i
   . (BiCCC k, KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b) => Free i (EXPO a b) -> Free i a -> Free i b
MkFree f $ MkFree g = MkFree (apply @(FBC (Id :: CAT k)) @a @b . (f &&& g) \\ fbcOb @a \\ fbcOb @b)

-- | Embed a morphism of the target category as a term between embedded objects.
lift :: forall {k} a b i. (BiCCC k, Ob (a :: k), Ob b) => a ~> b -> Free i (OBJ a) -> Free i (OBJ b)
lift f (MkFree g) = MkFree (Emb (Id f) . g)

fstSnd
  :: forall {k} a b i
   . (BiCCC k, KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b) => Free i (PROD a b) -> (Free i a, Free i b)
fstSnd (MkFree f) =
  (MkFree (fst @(FBC (Id :: CAT k)) @a @b . f), MkFree (snd @(FBC (Id :: CAT k)) @a @b . f)) \\ fbcOb @a \\ fbcOb @b

pattern (:&)
  :: (BiCCC k, KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b) => Free i a -> Free i b -> Free i (PROD a b)
pattern x :& y <- (fstSnd -> (x, y))
  where
    x :& y = MkFree (unFree x &&& unFree y)

{-# COMPLETE (:&) #-}

-- | Inject as the left\/right branch of a sum.
lft :: forall {k} a b i. (BiCCC k, KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b) => Free i a -> Free i (SUM a b)
lft (MkFree f) = MkFree (BC.lft @(FBC (Id :: CAT k)) @a @b . f \\ fbcOb @a \\ fbcOb @b)

rgt :: forall {k} a b i. (BiCCC k, KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b) => Free i b -> Free i (SUM a b)
rgt (MkFree f) = MkFree (BC.rgt @(FBC (Id :: CAT k)) @a @b . f \\ fbcOb @a \\ fbcOb @b)

-- | Uncurry a function term into the body of a 'lam' binding its argument.
uncurryF
  :: forall {k} a b i
   . (KnownCtx (i :: Ctx k), KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b)
  => Free i (EXPO a b) -> Free (a ': i) b
uncurryF f =
  withObExp @(FBC (Id :: CAT k)) @a @b
    (MkFree (apply @(FBC (Id :: CAT k)) @a @b . (unFree (tailT f) &&& unFree (headT @a @i))))
    \\ fbcOb @a
    \\ fbcOb @b

-- | Case analysis on a sum, in the presence of a shared context: distributes the context over
-- the sum (via 'distLProd', which any 'BiCCC' — hence the free one — gets for free) so each
-- branch still has access to it.
caseT
  :: forall {k} a b c i
   . (KnownCtx (i :: Ctx k), KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b)
  => Free i (SUM a b) -> Free (a ': i) c -> Free (b ': i) c -> Free i c
caseT m f g =
  MkFree ((unFree f ||| unFree g) . distLProd @(Mul i) @a @b . (id &&& unFree m) \\ ctxOb @i \\ fbcOb @a \\ fbcOb @b)

either
  :: forall {k} a b c i
   . (KnownCtx (i :: Ctx k), KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b, KnownFBCOb c)
  => Free i (EXPO a c) -> Free i (EXPO b c) -> Free i (SUM a b) -> Free i c
either f g m = caseT m (uncurryF f) (uncurryF g)

-- | Interpret a closed term (no free variables) into an actual morphism of the target
-- category, via 'lower' (a closed function-valued term needs no arguments to uncurry, since
-- its domain is already the monoidal unit) followed by 'interp' (with generators interpreted
-- by unwrapping 'Id' — the free category was built over @k@'s own hom-sets directly).
toCCC
  :: forall {k} a b
   . (BiCCC k, KnownFBCOb (a :: FBC (Id :: CAT k)), KnownFBCOb b) => Free '[] (EXPO a b) -> Lower a ~> Lower b
toCCC (MkFree f) = interp unId (lower @a @b f) \\ fbcOb @a \\ fbcOb @b

-- $
-- The examples below double as a regression test for the whole front end: each one exercises
-- 'lam'\/'Cast' (including nested lambdas), and\/or 'toCCC', on a concrete instantiation
-- (@k = 'Type'@) so the doctest can compare against an actual printed value.

-- | Inject as the right element of a sum.
--
-- >>> import Prelude (Bool (..))
-- >>> injectRight @Bool @Bool True
-- Right True
injectRight :: forall {k} (a :: k) b. (BiCCC k, Ob (a :: k), Ob b) => a ~> (b || a)
injectRight = toCCC @(F a) @(F b || F a) (lam (\x -> rgt x))

-- | Swap a product.
--
-- >>> import Prelude (Bool (..))
-- >>> swapProduct @Bool @Bool (True, False)
-- (False,True)
swapProduct :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => (a && b) ~> (b && a)
swapProduct = toCCC @(F a && F b) @(F b && F a) (lam (\p -> let (x :& y) = p in y :& x))

-- | Apply a function to an argument, both bundled in a product.
--
-- >>> import Prelude (Bool (..), not)
-- >>> applyPair @Bool @Bool (not, True)
-- False
applyPair :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => ((a ~~> b) && a) ~> b
applyPair = toCCC @((F a ~~> F b) && F a) @(F b) (lam (\p -> let (f :& a) = p in f $ a))

-- | Curry a pairing function.
--
-- >>> import Prelude (Bool (..))
-- >>> curryPair @Bool @Bool True False
-- (True,False)
curryPair :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => a ~> (b ~~> (a && b))
curryPair = toCCC @(F a) @(F b ~~> (F a && F b)) (lam (\x -> lam (\y -> x :& y)))

-- | Flip the argument order of a 3-argument curried function, applying the last argument
-- twice — exercises three levels of nested 'lam' and 'Cast' weakening across all of them.
--
-- >>> import Prelude (Bool (..))
-- >>> flipCurried3 @Bool @Bool @Bool (\_ a _ -> a) True False
-- True
flipCurried3 :: forall {k} a b c. (BiCCC k, Ob (a :: k), Ob b, Ob c) => (b ~~> a ~~> b ~~> c) ~> (a ~~> b ~~> c)
flipCurried3 =
  toCCC @(F b ~~> (F a ~~> (F b ~~> F c))) @(F a ~~> (F b ~~> F c))
    (lam (\x -> lam (\y -> lam (\z -> ((x $ z) $ y) $ z))))

-- | Swap a sum, via 'either'.
--
-- >>> import Prelude (Bool (..), Either (..))
-- >>> swapSum @Bool @Bool (Left True)
-- Right True
-- >>> swapSum @Bool @Bool (Right False)
-- Left False
swapSum :: forall {k} a b. (BiCCC k, Ob (a :: k), Ob b) => (a || b) ~> (b || a)
swapSum = toCCC @(F a || F b) @(F b || F a) (lam (\x -> either (lam (\y -> rgt y)) (lam (\y -> lft y)) x))

-- | Eliminate a sum by applying whichever of the two functions matches the branch actually
-- present.
--
-- >>> import Prelude (Bool (..), Either (..), not)
-- >>> caseEither @Bool @Bool @Bool (Left True, (not, id))
-- False
-- >>> caseEither @Bool @Bool @Bool (Right True, (not, id))
-- True
caseEither :: forall {k} (a :: k) b c. (BiCCC k, Ob a, Ob b, Ob c) => ((a || b) && ((a ~~> c) && (b ~~> c))) ~> c
caseEither =
  toCCC @((F a || F b) && ((F a ~~> F c) && (F b ~~> F c))) @(F c)
    (lam (\p -> let (ab :& q) = p in let (ac :& bc) = q in either ac bc ab))
