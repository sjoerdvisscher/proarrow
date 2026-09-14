{-# LANGUAGE AllowAmbiguousTypes #-}

{- HLINT ignore "Redundant $" -}

-- | A small HOAS (higher-order abstract syntax) front end for building morphisms in any
-- 'BiCCC', compiling through the free category of "Proarrow.Category.Instance.Free" with the
-- bicartesian closed structures rather than a bespoke one. A 'Free' term tracks its free
-- variables via a context list, the way a well-scoped lambda calculus does; 'lam' binds an
-- ordinary Haskell-level variable that 'Cast' automatically "weakens" across nested lambdas so
-- inner lambdas can still refer to outer ones. 'toCCC' interprets a closed term (no free
-- variables) into an actual morphism of the target category.
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
  , Syntax
  , BiCCCStructs
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

import Proarrow.Category.Instance.Free (FREE (..), Lower, emb, fold)
import Proarrow.Category.Monoidal (Monoidal)
import Proarrow.Category.Monoidal.Cartesian (BiCCC, Cartesian, prodToTensor, tensorToProd, unitToTerm)
import Proarrow.Category.Monoidal.Closed (Closed (..), lower)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts ((+++), (|||)), type (||))
import Proarrow.Colimit.BinaryCoproduct qualified as BC
import Proarrow.Colimit.Initial (HasInitialObject)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), type (*!))
import Proarrow.Limit.Terminal (HasTerminalObject, TermF)
import Proarrow.Object (Obj)
import Proarrow.Profunctor.Instance.Identity (Id (..))

infixr 0 $

-- | The structures of a bicartesian closed category as a list for 'FREE': the five BiCCC
-- classes, the 'Cartesian' marker supplying the formal @tensor = product@ coercions (the free
-- category cannot state that type equality itself), and 'Distributive', for case analysis in the
-- presence of a context.
type BiCCCStructs =
  '[ HasTerminalObject
   , HasInitialObject
   , HasBinaryProducts
   , HasBinaryCoproducts
   , Monoidal
   , Closed
   , Cartesian
   , Distributive
   ]

-- | The syntax category over @k@: the free BiCCC on @k@'s own hom-sets, i.e. 'Id' (rather than
-- @(~>)@ itself, which -- being an unsaturated type family application -- isn't allowed as a type
-- index wherever it is pattern-matched on below, in 'Mul').
type Syntax k = FREE BiCCCStructs (Id :: CAT k)

type Ctx k = [Syntax k]

-- | A short alias for embedding a base-category object, so type applications built from it read
-- like the target signature: '&&', '||' and '~~>' on the free category /are/ its object formers,
-- so @(F a ~~> F b) && F a@ is the object it looks like.
type F a = EMB a

-- | The context product: @'Mul' i@ is the single object standing in for "all the bound
-- variables in @i@", right fold with the most-recently-bound variable last -- the mirror image
-- of "Proarrow.Category.Monoidal.Strictified"'s @Fold@ (which puts its head /leftmost/), needed
-- here since 'curry'\/'fst'\/'snd' expect the thing being abstracted over on the /right/ of the
-- product, not the left, so @Fold@ itself can't be reused for this.
type family Mul (i :: Ctx k) :: Syntax k where
  Mul '[] = TermF
  Mul (a ': as) = Mul as *! a

-- | A term with free variables @i@ (innermost\/most-recently-bound first) and result type
-- @a@ -- literally a morphism from the context product to @a@ in the free BiCCC. A newtype
-- (rather than a bare type synonym) so that @i@ is recoverable from a 'Free' term's type: 'Mul'
-- is many-to-one at the type-family level as far as GHC's injectivity checker is concerned (even
-- though it's mathematically injective here), which would otherwise leave @i@ ambiguous wherever
-- it has to be inferred rather than given explicitly (e.g. picking which context a HOAS variable
-- reference in 'lam' denotes).
newtype Free (i :: Ctx k) (a :: Syntax k) = MkFree {unFree :: Mul i ~> a}

type KnownCtx :: forall {k}. Ctx k -> Constraint
class KnownCtx (i :: Ctx k) where
  ctxOb :: Obj (Mul i)

instance KnownCtx ('[] :: Ctx k) where
  ctxOb = id

instance (KnownCtx i, Ob (b :: Syntax k)) => KnownCtx (b ': i) where
  ctxOb = id \\ ctxOb @i

-- | The most-recently-bound variable.
headT :: forall {k} a i. (KnownCtx (i :: Ctx k), Ob (a :: Syntax k)) => Free (a ': i) a
headT = MkFree (snd @(Syntax k) @(Mul i) @a) \\ ctxOb @i

-- | Weaken a term by one more bound variable it doesn't use.
tailT :: forall {k} a i b. (KnownCtx (i :: Ctx k), Ob (a :: Syntax k)) => Free i b -> Free (a ': i) b
tailT (MkFree f) = MkFree (f . fst @(Syntax k) @(Mul i) @a) \\ ctxOb @i

-- | @'Cast' i j@ holds when context @i@ is context @j@ with zero or more extra variables
-- pushed on top, letting a term built for @j@ be used anywhere \"deeper\" than @j@.
type Cast :: forall {k}. Ctx k -> Ctx k -> Constraint
class Cast (i :: Ctx k) (j :: Ctx k) where
  cast :: (Ob (a :: Syntax k)) => Free j a -> Free i a

instance Cast i i where
  cast f = f

instance
  {-# OVERLAPPABLE #-}
  (Cast i j, KnownCtx (i :: Ctx k), Ob (b :: Syntax k), (b ': i) ~ i')
  => Cast i' j
  where
  cast f = tailT (cast f)

-- | Bind a variable, HOAS-style: the function argument stands for the newly bound variable,
-- usable (via 'Cast') in the body of this 'lam' and any 'lam' nested inside it. The body is a
-- morphism out of the context /product/; 'curry' wants the /tensor/, so the 'Cartesian'
-- coercion mediates.
lam
  :: forall {k} a b i
   . (KnownCtx (i :: Ctx k), Ob (a :: Syntax k), Ob b)
  => ((forall (x :: Ctx k). (Cast x (a ': i)) => Free x a) -> Free (a ': i) b)
  -> Free i (a ~~> b)
lam f = MkFree (curry @(Syntax k) @(Mul i) @a @b (unFree (f xa) . tensorToProd @(Mul i) @a)) \\ ctxOb @i
  where
    xa :: forall (x :: Ctx k). (Cast x (a ': i)) => Free x a
    xa = cast (headT @a @i)

-- | Function application.
($) :: forall {k} a b i. (Ob (a :: Syntax k), Ob b) => Free i (a ~~> b) -> Free i a -> Free i b
MkFree f $ MkFree g = MkFree (apply @(Syntax k) @a @b . prodToTensor @(a ~~> b) @a . (f &&& g))

-- | Embed a morphism of the target category as a term between embedded objects.
lift :: forall {k} a b i. (Ob (a :: k), Ob b) => a ~> b -> Free i (F a) -> Free i (F b)
lift f (MkFree g) = MkFree (emb (Id f) . g)

fstSnd :: forall {k} a b i. (Ob (a :: Syntax k), Ob b) => Free i (a && b) -> (Free i a, Free i b)
fstSnd (MkFree f) = (MkFree (fst @(Syntax k) @a @b . f), MkFree (snd @(Syntax k) @a @b . f))

pattern (:&) :: (Ob (a :: Syntax k), Ob b) => Free i a -> Free i b -> Free i (a && b)
pattern x :& y <- (fstSnd -> (x, y))
  where
    x :& y = MkFree (unFree x &&& unFree y)

{-# COMPLETE (:&) #-}

-- | Inject as the left\/right branch of a sum.
lft :: forall {k} a b i. (Ob (a :: Syntax k), Ob b) => Free i a -> Free i (a || b)
lft (MkFree f) = MkFree (BC.lft @(Syntax k) @a @b . f)

rgt :: forall {k} a b i. (Ob (a :: Syntax k), Ob b) => Free i b -> Free i (a || b)
rgt (MkFree f) = MkFree (BC.rgt @(Syntax k) @a @b . f)

-- | Uncurry a function term into the body of a 'lam' binding its argument.
uncurryF
  :: forall {k} a b i
   . (KnownCtx (i :: Ctx k), Ob (a :: Syntax k), Ob b)
  => Free i (a ~~> b) -> Free (a ': i) b
uncurryF f = MkFree (apply @(Syntax k) @a @b . prodToTensor @(a ~~> b) @a . (unFree (tailT f) &&& unFree (headT @a @i)))

-- | Case analysis on a sum, in the presence of a shared context: distributes the context over
-- the sum, so each branch still has access to it. The free category's distributivity is stated
-- for the tensor, so the product is coerced to the tensor and back around 'distL'.
caseT
  :: forall {k} a b c i
   . (KnownCtx (i :: Ctx k), Ob (a :: Syntax k), Ob b)
  => Free i (a || b) -> Free (a ': i) c -> Free (b ': i) c -> Free i c
caseT m f g =
  MkFree
    ( (unFree f ||| unFree g)
        . (tensorToProd @(Mul i) @a +++ tensorToProd @(Mul i) @b)
        . distL @(Syntax k) @(Mul i) @a @b
        . prodToTensor @(Mul i) @(a || b)
        . (id &&& unFree m)
    )
    \\ ctxOb @i

either
  :: forall {k} a b c i
   . (KnownCtx (i :: Ctx k), Ob (a :: Syntax k), Ob b, Ob c)
  => Free i (a ~~> c) -> Free i (b ~~> c) -> Free i (a || b) -> Free i c
either f g m = caseT m (uncurryF f) (uncurryF g)

-- | Interpret a closed term (no free variables) into an actual morphism of the target
-- category: move the empty context from the terminal object to the monoidal unit, 'lower' the
-- function-valued term (a closed one needs no arguments to uncurry), and 'fold' into @k@ with
-- generators interpreted by unwrapping 'Id' -- the free category was built over @k@'s own
-- hom-sets directly.
toCCC
  :: forall {k} a b
   . (BiCCC k, Ob (a :: Syntax k), Ob b)
  => Free '[] (a ~~> b) -> Lower (Id :: CAT k) a ~> Lower (Id :: CAT k) b
toCCC (MkFree f) = fold @BiCCCStructs @(Id :: CAT k) unId (lower @a @b (f . unitToTerm))

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
flipCurried3
  :: forall {k} a b c. (BiCCC k, Ob (a :: k), Ob b, Ob c) => (b ~~> a ~~> b ~~> c) ~> (a ~~> b ~~> c)
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
caseEither
  :: forall {k} (a :: k) b c. (BiCCC k, Ob a, Ob b, Ob c) => ((a || b) && ((a ~~> c) && (b ~~> c))) ~> c
caseEither =
  toCCC @((F a || F b) && ((F a ~~> F c) && (F b ~~> F c))) @(F c)
    (lam (\p -> let (ab :& q) = p in let (ac :& bc) = q in either ac bc ab))
