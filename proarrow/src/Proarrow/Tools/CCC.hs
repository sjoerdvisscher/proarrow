{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Cartesian terms, using the syntax and binders of "Proarrow.Tools.SMC" in 'PROD' @k@.
-- Its tensor is the product of @k@, independently of any monoidal structure on @k@ itself.
-- 'F' embeds a base object, @a ':**' b@ is a product, and @a ':->' b@ is the exponential
-- of 'PROD' @k@. 'toCCC' compiles a function on terms and unwraps the resulting arrow into @k@.
--
-- Each operation asks only for the structure it uses: products for pairing and binding,
-- 'Closed' @('PROD' k)@ for 'lam' and '(!)', coproducts for 'inl' and 'inr', and
-- 'Proarrow.Category.Monoidal.Distributive.Distributive' @('PROD' k)@ for 'caseOf'. Copying and
-- discarding are supplied by products. The patterns, contexts and @QualifiedDo@ notation are
-- those of SMC; see "Proarrow.Tools.SMC" for their use, including 'recast' across binding depths.
--
-- > import Prelude hiding ((**))
-- > import Proarrow.Tools.CCC (SYN (..), type F, toCCC, (**))
-- >
-- > swapProduct = toCCC @(F a :** F b) @(F b :** F a) (\(a, b) -> b ** a)
module Proarrow.Tools.CCC
  ( -- * Types
    SYN (I, (:**), (:->), (:&&), Top, (:||), Zero)
  , type F
  , Interp
  , KnownObj

    -- * Terms

    -- ** Products
  , Term
  , toCCC
  , lift
  , liftF
  , (-<)
  , returnA
  , unit
  , (**)
  , split
  , Tuple
  , TupleCtx
  , TupleDepth
  , recast
  , with
  , exl
  , exr
  , absorb

    -- ** Product exponentials
  , lam
  , (!)

    -- ** Coproducts
  , inl
  , inr
  , caseOf
  , absurd

    -- * Contexts
  , Ctx
  , KnownCtx
  , Union
  , Merge
  , Thin
  , BindVar

    -- * Do notation
  , (>>=)
  , return
  , fail
  , Bind
  , Binds

    -- * Examples
  , injectRight
  , swapProduct
  , applyPair
  , curryPair
  , flipCurried3
  , swapSum
  , caseEither
  ) where

import Proarrow.Category.Monoidal.Cartesian ()
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Distributive (Distributive)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts, type (||))
import Proarrow.Core (CategoryOf (..), Is, UN)
import Proarrow.Limit.BinaryProduct (HasProducts, PROD (..), Prod (..), type (&&))
import Proarrow.Tools.SMC hiding (F, Interp, lift, liftF, (-<))
import Proarrow.Tools.SMC qualified as SMC
import Prelude (uncurry)

-- | A base-category object in the SMC syntax over 'PROD' @k@.
type F :: k -> SYN (PROD k)
type F a = SMC.F (PR a)

-- | The base-category object a cartesian type expression stands for.
type Interp :: SYN (PROD k) -> k
type Interp a = UN PR (SMC.Interp a)

-- | Compile a function on terms into an arrow of @k@. The input arrives through an SMC pattern,
-- a variable, @()@, or a tuple, and the body's operations determine the additional structure needed.
{-# INLINE toCCC #-}
toCCC
  :: forall {k} (a :: SYN (PROD k)) b t cont
   . (HasProducts k, Binds 0 '[] a b t cont)
  => (t -> cont) -> Interp a ~> Interp b
toCCC f = case SMC.toSMC @a @b f of Prod g -> g

-- | Lift a base-category arrow onto terms. The type expressions can be composite, as in SMC's
-- 'Proarrow.Tools.SMC.lift'; use type applications when their interpretations do not determine them.
{-# INLINE lift #-}
lift
  :: forall {k} (a :: SYN (PROD k)) b d g
   . (CategoryOf k, Is PR (SMC.Interp a), Is PR (SMC.Interp b))
  => Interp a ~> Interp b -> Term d g a -> Term d g b
lift f = SMC.lift @a @b (Prod f)

-- | Lift a base-category arrow onto a term or tuple of terms, embedding its result by 'F'.
-- The result object is inferred from the arrow. Use 'lift' for composite result syntax.
{-# INLINE liftF #-}
liftF
  :: forall {k} (a :: SYN (PROD k)) b t
   . (CategoryOf k, Is PR (SMC.Interp a), Tuple (PROD k) t a)
  => (Interp a ~> b) -> t -> Term (TupleDepth t) (TupleCtx (PROD k) t) (F b)
liftF f = SMC.liftF @a @(PR b) (Prod f)

infixr 0 -<

-- | Arrow application, mirroring @f -< x@ in Haskell's arrow notation.
-- This is infix 'liftF': the input may be a term or tuple, and the result is embedded by 'F'.
-- The @Arrows@ extension must be disabled, since it reserves this symbol.
{-# INLINE (-<) #-}
(-<)
  :: forall {k} (a :: SYN (PROD k)) b t
   . (CategoryOf k, Is PR (SMC.Interp a), Tuple (PROD k) t a)
  => (Interp a ~> b) -> t -> Term (TupleDepth t) (TupleCtx (PROD k) t) (F b)
(-<) = liftF @a @b

-- | Inject as the right element of a sum.
--
-- >>> import Prelude (Bool (..))
-- >>> injectRight @Bool @Bool True
-- Right True
injectRight
  :: forall {k} (a :: k) b. (HasProducts k, HasBinaryCoproducts k, Ob a, Ob b) => a ~> (b || a)
injectRight = toCCC @(F a) @(F b :|| F a) (\x -> inr x)

-- | Swap a product. Only products are needed.
--
-- >>> import Prelude (Bool (..))
-- >>> swapProduct @Bool @Bool (True, False)
-- (False,True)
swapProduct
  :: forall {k} (a :: k) b. (HasProducts k, Ob a, Ob b) => (a && b) ~> (b && a)
swapProduct = toCCC @(F a :** F b) @(F b :** F a) (\(x, y) -> y ** x)

-- | Apply a function to an argument, both bundled in a product.
--
-- >>> import Prelude (Bool (..), not)
-- >>> applyPair @Bool @Bool (not, True)
-- False
applyPair
  :: forall {k} (a :: k) b
   . (HasProducts k, Closed (PROD k), Ob a, Ob b)
  => Interp ((F a :-> F b) :** F a) ~> b
applyPair = toCCC @((F a :-> F b) :** F a) @(F b) (uncurry (!))

-- | Curry a pairing function.
--
-- >>> import Prelude (Bool (..))
-- >>> curryPair @Bool @Bool True False
-- (True,False)
curryPair
  :: forall {k} (a :: k) b
   . (HasProducts k, Closed (PROD k), Ob a, Ob b)
  => a ~> Interp (F b :-> (F a :** F b))
curryPair = toCCC @(F a) @(F b :-> (F a :** F b)) (\x -> lam (\y -> x ** y))

-- | Flip the first two arguments of a curried function, supplying its third argument from the
-- second as well. Nested binders and a repeated variable use SMC's contexts.
--
-- >>> import Prelude (Bool (..))
-- >>> flipCurried3 @Bool @Bool @Bool (\_ a _ -> a) True False
-- True
flipCurried3
  :: forall {k} (a :: k) b c
   . (HasProducts k, Closed (PROD k), Ob a, Ob b, Ob c)
  => Interp (F b :-> F a :-> F b :-> F c) ~> Interp (F a :-> F b :-> F c)
flipCurried3 =
  toCCC @(F b :-> F a :-> F b :-> F c) @(F a :-> F b :-> F c)
    (\x -> lam (\y -> lam (\z -> x ! z ! y ! z)))

-- | Swap a sum by case analysis. No exponentials are needed.
--
-- >>> import Prelude (Bool (..), Either (..))
-- >>> swapSum @Bool @Bool (Left True)
-- Right True
-- >>> swapSum @Bool @Bool (Right False)
-- Left False
swapSum
  :: forall {k} (a :: k) b
   . (HasProducts k, Distributive (PROD k), Ob a, Ob b)
  => (a || b) ~> (b || a)
swapSum = toCCC @(F a :|| F b) @(F b :|| F a) (\x -> caseOf x inr inl)

-- | Apply whichever function matches the branch of a sum. The functions are shared with the
-- selected branch through the context.
--
-- >>> import Prelude (Bool (..), Either (..), id, not)
-- >>> caseEither @Bool @Bool @Bool (Left True, (not, id))
-- False
-- >>> caseEither @Bool @Bool @Bool (Right True, (not, id))
-- True
caseEither
  :: forall {k} (a :: k) b c
   . (HasProducts k, Closed (PROD k), Distributive (PROD k), Ob a, Ob b, Ob c)
  => Interp ((F a :|| F b) :** ((F a :-> F c) :** (F b :-> F c))) ~> c
caseEither =
  withObExp @(PROD k) @(PR a) @(PR c)
    ( withObExp @(PROD k) @(PR b) @(PR c)
        ( toCCC @((F a :|| F b) :** ((F a :-> F c) :** (F b :-> F c))) @(F c)
            (\(ab, (ac, bc)) -> caseOf ab (\a -> ac ! a) (\b -> bc ! b))
        )
    )
