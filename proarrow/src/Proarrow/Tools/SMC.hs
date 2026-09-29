{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | A small HOAS front end for building morphisms in any symmetric monoidal category, the linear
-- counterpart of "Proarrow.Tools.CCC". Each variable is used exactly once: the functions on terms
-- are linear, so GHC's linear types check that every variable is used once, and a 'Term' is
-- indexed by its context, which is exactly the variables it uses. So a variable is the identity
-- on its own type, and no copying or discarding is ever generated. Terms with disjoint contexts
-- combine by merging the contexts, which only reorders wires. Functions on terms need
-- @LinearTypes@ and linear arrows, e.g. @'Term' d g a %1 -> 'Term' d g b@.
--
-- Types are 'SYN' expressions, interpreted in the target category by 'Interp'. Their tensor is a
-- constructor, so 'split' can take a term's type apart, which the target's own @**@, a type
-- family, would not allow.
--
-- Every variable has an id, the number of binders around it, and a context lists its variables
-- by descending id. Merging compares ids, so it only reduces where the depths are known, which is
-- the case for terms built directly inside 'toSMC'. A reusable piece that binds variables of its
-- own is compiled on its own and used through 'call'.
--
-- The module also provides @do@ notation, for use with @QualifiedDo@:
--
-- > import Proarrow.Tools.SMC (SYN (..), toSMC, (*))
-- > import Proarrow.Tools.SMC qualified as SMC
-- >
-- > rotT = toSMC @(F a :** F b :** F c) \x -> SMC.do
-- >   ((a, b), c) <- x
-- >   b * c * a
--
-- A bind takes its right hand side apart with a pattern of (nested) pairs, as 'split' does, and
-- the rest of the block must use every variable exactly once.
--
-- With @RecursiveDo@, a @rec@ block traces, so it needs a traced monoidal category. Its variables
-- that are used before they are bound are fed back, and the others are passed on to the rest of
-- the block. GHC's translation of @rec@ passes every variable of the block to its end again,
-- including the ones a later statement of the block already used, so only such blocks work
-- where no statement uses a variable bound by an earlier one. A block of a single statement always
-- qualifies, and a nested pattern lets one statement bind everything:
--
-- > rec ((am, bp), (bm, cp)) <- lift g (ap * bm) * lift f (bp * cm)
--
-- 'loop' traces without GHC's translation, so it has neither restriction, but the type of the fed
-- back variable has to be given.
--
-- The approach follows /Evaluating Linear Functions to Symmetric Monoidal Categories/, whose
-- @P k r a@ ports correspond to 'Term', @encode@ to 'lift', @decode@ to 'toSMC', @(!:)@ to
-- '(*)' and @split@ to 'split'. It keeps the context thinned instead of computing in the
-- cartesian structure and arguing afterwards that the result is monoidal.
module Proarrow.Tools.SMC
  ( -- * Types
    SYN (..)
  , Interp
  , KnownObj (..)
  , synOb

    -- * Terms
  , Term (..)
  , toSMC
  , lift
  , dup
  , drop
  , call
  , (*)
  , split
  , unit
  , lam
  , loop
  , produce
  , annihilate
  , ($$)

    -- * Contexts
  , Ctx
  , Mul
  , KnownCtx
  , ctxOb
  , withCtxOb
  , Union
  , UnionBy
  , Merge (..)
  , MergeBy (..)
  , snoc
  , push2

    -- * Do notation
  , (>>=)
  , return
  , mfix
  , fail
  , Bind
  , Pat (..)
  , PSize
  , PCtx
  , Ret (..)
  , unRet
  , Rec (..)
  , RecVars (..)

    -- * Examples
  , swapT
  , applyT
  , curryT
  , rotT
  , traceT
  , loopT
  , loopCC
  , snakeT
  , combineDualT
  ) where

import Data.Kind (Constraint, Type)
import GHC.Exts (Multiplicity (..))
import GHC.TypeLits (ErrorMessage (..), TypeError)
import GHC.TypeNats (CmpNat, Nat, type (+))
import Prelude (Ordering (..), type (~))
import Prelude qualified as P

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , Tensor
  , associator'
  , associatorInv'
  )
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal, trace)
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object (Obj)

infixl 7 *
infixl 8 $$
infixl 7 :**
infixr 5 :->

-- | Type expressions over the objects of @k@: an object of @k@, the unit, the tensor, the
-- internal hom and the dual.
type data SYN k = F k | I | SYN k :** SYN k | SYN k :-> SYN k | D (SYN k)

-- | The object of @k@ a type expression stands for.
type Interp :: forall {k}. SYN k -> k
type family Interp s where
  Interp (F a) = a
  Interp I = Unit
  Interp (a :** b) = Interp a ** Interp b
  Interp (a :-> b) = Interp a ~~> Interp b
  Interp (D a) = Dual (Interp a)

type KnownObj :: forall {k}. SYN k -> Constraint
class (CategoryOf k) => KnownObj (s :: SYN k) where
  withSynOb :: ((Ob (Interp s)) => r) -> r

instance (CategoryOf k, Ob (a :: k)) => KnownObj (F a) where
  withSynOb r = r

instance (Monoidal k) => KnownObj (I :: SYN k) where
  withSynOb r = r

instance (Monoidal k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :** b) where
  withSynOb r = withSynOb @a (withSynOb @b (withOb2 @k @(Interp a) @(Interp b) r))

instance (Closed k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :-> b) where
  withSynOb r = withSynOb @a (withSynOb @b (withObExp @k @(Interp a) @(Interp b) r))

instance (StarAutonomous k, KnownObj (a :: SYN k)) => KnownObj (D a) where
  withSynOb r = withSynOb @a (withObDual @k @(Interp a) r)

-- | The identity on the object a type expression stands for.
synOb :: forall {k} (s :: SYN k). (KnownObj s) => Obj (Interp s)
synOb = withSynOb @s (obj @(Interp s))

-- | A context: the variables a term uses, each with its id and type, by descending id.
type Ctx :: Type -> Type
type Ctx k = [(Nat, SYN k)]

-- | The type standing in for a context: the tensor of its variables' types, with the most
-- recently bound variable on the right. A single variable is just its type, so a variable is the
-- identity. The cost is that @Mul ('(n, a) ': g)@ only reduces once @g@ is known to be empty or
-- not, which 'ctxCase' tells.
type Mul :: forall {k}. Ctx k -> SYN k
type family Mul g where
  Mul '[] = I
  Mul '[ '(n, a)] = a
  Mul ('(n, a) ': g) = Mul g :** a

-- | A term at binding depth @d@ with context @g@ and type @a@: a morphism from the tensor of
-- the context to @a@.
type Term :: forall {k}. Nat -> Ctx k -> SYN k -> Type
data Term d g a where
  MkTerm :: (Interp (Mul g) ~> Interp a) %Many -> Term d g a

-- | A context that is known to be empty or not, all the way down.
type KnownCtx :: forall {k}. Ctx k -> Constraint
class KnownCtx (g :: Ctx k) where
  -- | Case analysis on the context, which is what lets @'Mul' ('(n, a) ': g)@ reduce.
  ctxCase :: ((g ~ '[]) => r) -> (forall n a g'. (g ~ ('(n, a) ': g'), KnownObj a, KnownCtx g') => r) -> r

instance KnownCtx ('[] :: Ctx k) where
  ctxCase e _ = e

instance (KnownObj a, KnownCtx g) => KnownCtx ('(n, a) ': g) where
  ctxCase _ c = c

-- | The tensor of a context is an object.
withCtxOb :: forall {k} (g :: Ctx k) r. (Monoidal k, KnownCtx g) => ((Ob (Interp (Mul g))) => r) -> r
withCtxOb r =
  ctxCase @g
    r
    ( \ @_ @a @g' ->
        ctxCase @g' (withSynOb @a r) (withCtxOb @g' (withSynOb @a (withOb2 @k @(Interp (Mul g')) @(Interp a) r)))
    )

-- | The identity on the tensor of a context.
ctxOb :: forall {k} (g :: Ctx k). (Monoidal k, KnownCtx g) => Obj (Interp (Mul g))
ctxOb = withCtxOb @g (obj @(Interp (Mul g)))

-- | A new variable on the right of a context: a unitor if the context was empty, and nothing
-- otherwise.
snoc
  :: forall {k} n (a :: SYN k) g
   . (Monoidal k, KnownObj a, KnownCtx g) => Interp (Mul g) ** Interp a ~> Interp (Mul ('(n, a) ': g))
snoc = ctxCase @g (withSynOb @a leftUnitor) (ctxOb @('(n, a) ': g))

-- | The context of two terms used side by side.
type Union :: forall {k}. Ctx k -> Ctx k -> Ctx k
type family Union g1 g2 where
  Union '[] g2 = g2
  Union g1 '[] = g1
  Union ('(n, a) ': g1) ('(m, b) ': g2) = UnionBy (CmpNat n m) ('(n, a) ': g1) ('(m, b) ': g2)

type UnionBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Ctx k
type family UnionBy o g1 g2 where
  UnionBy GT (x ': g1) g2 = x ': Union g1 g2
  UnionBy LT g1 (y ': g2) = y ': Union g1 g2
  UnionBy EQ _ _ = TypeError (Text "Proarrow.Tools.SMC: a variable is used more than once")

-- | Split the tensor of a merged context into the tensors of the two contexts it came from, and
-- back. This is where the wires are reordered, and the only place 'swap' is used.
type Merge :: forall {k}. Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => Merge (g1 :: Ctx k) g2 where
  merge :: Interp (Mul (Union g1 g2)) ~> Interp (Mul g1) ** Interp (Mul g2)
  unmerge :: Interp (Mul g1) ** Interp (Mul g2) ~> Interp (Mul (Union g1 g2))

instance (Monoidal k, KnownCtx g2) => Merge ('[] :: Ctx k) g2 where
  merge = withCtxOb @g2 leftUnitorInv
  unmerge = withCtxOb @g2 leftUnitor

instance (Monoidal k, KnownCtx ('(n, a) ': g1)) => Merge ('(n, a) ': g1 :: Ctx k) '[] where
  merge = withCtxOb @('(n, a) ': g1) rightUnitorInv
  unmerge = withCtxOb @('(n, a) ': g1) rightUnitor

instance
  ( Monoidal k
  , KnownObj a
  , KnownObj b
  , KnownCtx g1
  , KnownCtx g2
  , MergeBy (CmpNat n m) ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  )
  => Merge ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  where
  merge = mergeBy @(CmpNat n m) @('(n, a) ': g1) @('(m, b) ': g2)
  unmerge = unmergeBy @(CmpNat n m) @('(n, a) ': g1) @('(m, b) ': g2)

-- | 'merge' and 'unmerge' for two non-empty contexts, by which of the two has the larger head id.
type MergeBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => MergeBy o (g1 :: Ctx k) g2 where
  mergeBy :: Interp (Mul (UnionBy o g1 g2)) ~> Interp (Mul g1) ** Interp (Mul g2)
  unmergeBy :: Interp (Mul g1) ** Interp (Mul g2) ~> Interp (Mul (UnionBy o g1 g2))

-- The union of two non-empty contexts is not empty, so its tensor splits off the newest variable
-- as is, which the equality says for GHC. If the newest variable is alone on its side, merging is
-- one swap or nothing.
instance
  ( SymMonoidal k
  , Merge g1 ('(m, b) ': g2)
  , KnownObj (a :: SYN k)
  , KnownObj b
  , Mul ('(n, a) ': Union g1 ('(m, b) ': g2)) ~ (Mul (Union g1 ('(m, b) ': g2)) :** a)
  )
  => MergeBy GT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  mergeBy =
    withCtxOb @('(m, b) ': g2)
      ( withSynOb @a
          ( ctxCase @g1
              (swap @k @(Interp (Mul ('(m, b) ': g2))) @(Interp a))
              ( associatorInv' (ctxOb @g1) (synOb @a) (ctxOb @('(m, b) ': g2))
                  . (ctxOb @g1 ** swap @k @(Interp (Mul ('(m, b) ': g2))) @(Interp a))
                  . associator' (ctxOb @g1) (ctxOb @('(m, b) ': g2)) (synOb @a)
                  . (merge @g1 @('(m, b) ': g2) ** synOb @a)
              )
          )
      )
  unmergeBy =
    withCtxOb @('(m, b) ': g2)
      ( withSynOb @a
          ( ctxCase @g1
              (swap @k @(Interp a) @(Interp (Mul ('(m, b) ': g2))))
              ( (unmerge @g1 @('(m, b) ': g2) ** synOb @a)
                  . associatorInv' (ctxOb @g1) (ctxOb @('(m, b) ': g2)) (synOb @a)
                  . (ctxOb @g1 ** swap @k @(Interp a) @(Interp (Mul ('(m, b) ': g2))))
                  . associator' (ctxOb @g1) (synOb @a) (ctxOb @('(m, b) ': g2))
              )
          )
      )

instance
  ( Monoidal k
  , Merge ('(n, a) ': g1) g2
  , KnownObj a
  , KnownObj (b :: SYN k)
  , Mul ('(m, b) ': Union ('(n, a) ': g1) g2) ~ (Mul (Union ('(n, a) ': g1) g2) :** b)
  )
  => MergeBy LT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  mergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( associator' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
          . (merge @('(n, a) ': g1) @g2 ** synOb @b)
      )
  unmergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( (unmerge @('(n, a) ': g1) @g2 ** synOb @b)
          . associatorInv' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
      )

-- | The variable with id @n@: the identity on its type.
var :: forall {k} n (a :: SYN k) d. (CategoryOf k, KnownObj a) => Term d '[ '(n, a)] a
var = withSynOb @a (MkTerm (obj @(Interp a)))

-- | Compile a function on terms, whose argument is used exactly once, to a morphism.
toSMC
  :: forall {k} (a :: SYN k) b d
   . (Monoidal k, KnownObj a)
  => (Term d '[ '(0, a)] a %1 -> Term 1 '[ '(0, a)] b)
  -> Interp a ~> Interp b
toSMC k = case k (var @0 @a) of MkTerm f -> f

-- | Copy a term whose type is a comonoid, in "Proarrow.Tools.SMC": @(x1, x2) <- dup x@.
dup :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s %1 -> Term d g (s :** s)
dup = lift @s @(s :** s) comult

-- | Discard a term whose type is a comonoid, in "Proarrow.Tools.SMC": @() <- drop x@.
drop :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s %1 -> Term d g I
drop = lift @s @I counit

-- | Lift a morphism of the target category to a function on terms.
lift :: forall {k} (a :: SYN k) b d g. (CategoryOf k) => (Interp a ~> Interp b) -> Term d g a %1 -> Term d g b
lift f (MkTerm t) = MkTerm (f . t)

-- | Use a function on terms inside another term, compiled on its own with 'toSMC'. This is how
-- a reusable piece that binds variables of its own is used, and unlike 'lift' of the compiled
-- morphism it needs no type annotations.
call
  :: forall {k} (a :: SYN k) b d g d'
   . (Monoidal k, KnownObj a)
  => (Term d' '[ '(0, a)] a %1 -> Term 1 '[ '(0, a)] b)
  -> Term d g a
  %1 -> Term d g b
call f = lift (toSMC f)

-- | Two terms side by side. Their contexts must be disjoint.
(*)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Monoidal k, Merge g1 g2)
  => Term d g1 a %1 -> Term d g2 b %1 -> Term d (Union g1 g2) (a :** b)
MkTerm f * MkTerm g = MkTerm ((f ** g) . merge @g1 @g2)

-- | Two new variables @(n, a)@ and @(m, b)@ on the right of the context @r@, for 'split'. When @r@
-- is empty the pair is the whole context.
push2
  :: forall {k} r n (a :: SYN k) m b g
   . (Monoidal k, KnownObj a, KnownObj b, Merge r g)
  => (Interp (Mul g) ~> Interp a ** Interp b)
  -> Interp (Mul (Union r g)) ~> Interp (Mul ('(m, b) ': '(n, a) ': r))
push2 p =
  ctxCase @r
    p
    (associatorInv' (ctxOb @r) (synOb @a) (synOb @b) . (ctxOb @r ** p) . merge @r @g)

-- | Take a tensor apart: the continuation gets a variable for each side and must use both.
split
  :: forall {k} d g r (a :: SYN k) b c da db
   . (Monoidal k, KnownObj a, KnownObj b, Merge r g)
  => Term d g (a :** b)
  %1 -> ( Term da '[ '(d, a)] a
          %1 -> Term db '[ '(d + 1, b)] b
          %1 -> Term (d + 2) ('(d + 1, b) ': '(d, a) ': r) c
        )
  %1 -> Term d (Union r g) c
split (MkTerm p) k = case k (var @d @a) (var @(d + 1) @b) of
  MkTerm body -> MkTerm (body . push2 @r @d @a @(d + 1) @b @g p)

-- | The unit, which uses no variables.
unit :: forall {k} d. (Monoidal k) => Term d ('[] :: Ctx k) I
unit = MkTerm id

-- | Bind a variable, which the body must use exactly once. This needs the category to be closed.
lam
  :: forall {k} d r (a :: SYN k) b da
   . (Closed k, KnownObj a, KnownCtx r)
  => (Term da '[ '(d, a)] a %1 -> Term (d + 1) ('(d, a) ': r) b)
  %1 -> Term d r (a :-> b)
lam k = case k (var @d @a) of
  MkTerm body -> withCtxOb @r (withSynOb @a (MkTerm (curry @k @(Interp (Mul r)) @(Interp a) (body . snoc @d @a @r))))

-- | Trace: bind a variable for the value fed back, which the body must use exactly once, and
-- return it again next to the result. This needs the category to be traced.
loop
  :: forall {k} (u :: SYN k) b d r du
   . (TracedMonoidal k, KnownObj u, KnownObj b, KnownCtx r)
  => (Term du '[ '(d, u)] u %1 -> Term (d + 1) ('(d, u) ': r) (b :** u))
  %1 -> Term d r b
loop k = case k (var @d @u) of
  MkTerm body ->
    withCtxOb @r
      ( withSynOb @u
          (withSynOb @b (MkTerm (trace @(~>) @(Interp u) @(Interp (Mul r)) @(Interp b) (body . snoc @d @u @r))))
      )

-- | A new pair of wires, a variable and its dual, from nothing: the unit of the duality. This
-- needs the category to be compact closed.
produce :: forall {k} (a :: SYN k) d. (CompactClosed k, KnownObj a) => Term d '[] (a :** D a)
produce = withSynOb @a (MkTerm (dualityUnit @k @(Interp a)))

-- | Join a dual and its wire into nothing: the counit of the duality.
annihilate
  :: forall {k} (a :: SYN k) d g1 g2
   . (CompactClosed k, KnownObj a, Merge g1 g2)
  => Term d g1 (D a) %1 -> Term d g2 a %1 -> Term d (Union g1 g2) I
annihilate (MkTerm x) (MkTerm y) = withSynOb @a (MkTerm (dualityCounit @k @(Interp a) . (x ** y) . merge @g1 @g2))

-- | Function application. The function and its argument must have disjoint contexts.
($$)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Closed k, KnownObj a, KnownObj b, Merge g1 g2)
  => Term d g1 (a :-> b) %1 -> Term d g2 a %1 -> Term d (Union g1 g2) b
MkTerm f $$ MkTerm x =
  withSynOb @a (withSynOb @b (MkTerm (apply @k @(Interp a) @(Interp b) . (f ** x) . merge @g1 @g2)))

-- Do notation

-- | A bind in a @do@ block: a term taken apart by a pattern, or the variables of a @rec@ block.
-- The multiplicity @p@ of the continuation depends only on the right hand side @m@, since GHC
-- needs it before it knows the rest.
type Bind :: Type -> Type -> Type -> Multiplicity -> Type -> Type -> Constraint
class Bind k m t p cont r | m -> k p where
  (>>=) :: m %1 -> (t %p -> cont) %1 -> r

-- The types of the continuation and the result are matched with equalities, so that the
-- instance is chosen as soon as the right hand side is known.
instance
  {-# INCOHERENT #-}
  ( cont ~ Term (d + PSize t) (CtxOf @k cont) (TyOf @k cont)
  , r ~ Term d (PCtx t d g a (CtxOf @k cont)) (TyOf @k cont)
  , Pat k t d g a (CtxOf @k cont) (TyOf @k cont)
  )
  => Bind k (Term d g (a :: SYN k)) t One cont r
  where
  (>>=) = pat @k @t @d @g @a @(CtxOf @k cont) @(TyOf @k cont)

-- | The statement of a @rec@ block, whose continuation is its 'return'.
instance
  (Bind k (Term d g a) t One cont r', r ~ Ret tt r')
  => Bind k (Term d g (a :: SYN k)) t One (Ret tt cont) r
  where
  x >>= k = Ret (x >>= \p -> unRet (k p))

-- | The body of a @rec@ block, tagged with the tuple of its variables. GHC's translation passes
-- that tuple to both 'return' and 'mfix', and this tag is what makes them the same.
type Ret :: Type -> Type -> Type
newtype Ret t x = Ret x

unRet :: Ret t x %1 -> x
unRet (Ret x) = x

-- | A pattern: a variable, or a pair of patterns. Binding it at depth @d@ to a term with context
-- @g@ and type @a@, with a continuation with context @g'@ and type @c@.
type Pat :: forall k -> Type -> Nat -> Ctx k -> SYN k -> Ctx k -> SYN k -> Constraint
class Pat k t d g a g' c where
  pat :: Term d g a %1 -> (t %1 -> Term (d + PSize t) g' c) %1 -> Term d (PCtx t d g a g') c

-- | The number of variables a pattern binds on the way, and so the depth it adds.
type PSize :: Type -> Nat
type family PSize t where
  PSize (x, y) = 2 + PSize x + PSize y
  PSize t = 0

-- | The context of a pattern match, from the context of the right hand side and of the
-- continuation.
type PCtx :: forall {k}. Type -> Nat -> Ctx k -> SYN k -> Ctx k -> Ctx k
type family PCtx t d g a g' where
  PCtx (x, y) d g (a1 :** a2) g' = Union (Drop2 (PCtxPair x y d a1 a2 g')) g
  PCtx () d g a g' = Union g g'
  PCtx t d g a g' = g'

-- | The context of the body of the 'split' that a pair pattern starts with.
type PCtxPair :: forall {k}. Type -> Type -> Nat -> SYN k -> SYN k -> Ctx k -> Ctx k
type PCtxPair x y d a1 a2 g' =
  PCtx x (d + 2) '[ '(d, a1)] a1 (PCtx y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g')

-- Both instances are incoherent: a variable pattern's type is often still unknown when the
-- instance is chosen, and a pair pattern's type is always a pair by then.

-- | The pattern @()@ uses up a term of the unit type.
instance {-# INCOHERENT #-} (Monoidal k, a ~ I, KnownObj c, Merge g g') => Pat k () d g (a :: SYN k) g' c where
  pat (MkTerm u) k = case k () of
    MkTerm t -> withSynOb @c (MkTerm (leftUnitor @k @(Interp c) . (u ** t) . merge @g @g'))

instance {-# INCOHERENT #-} (t ~ Term (DepthOf t) g a) => Pat k t d g a g' c where
  pat x k = k (retag x)

instance
  {-# INCOHERENT #-}
  ( Monoidal k
  , a ~ (a1 :** a2)
  , KnownObj a1
  , KnownObj a2
  , Pat k x (d + 2) '[ '(d, a1)] a1 (PCtx y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g') c
  , Pat k y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g' c
  , d + 2 + PSize x + PSize y ~ d + PSize (x, y)
  , PCtxPair x y d a1 a2 g' ~ ('(d + 1, a2) ': '(d, a1) ': Drop2 (PCtxPair x y d a1 a2 g'))
  , Merge (Drop2 (PCtxPair x y d a1 a2 g')) g
  )
  => Pat k (x, y) d g (a :: SYN k) g' c
  where
  pat s k =
    split
      s
      ( \a b ->
          pat @k @x @(d + 2) @'[ '(d, a1)] @a1 @(PCtx y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g') @c
            a
            (\px -> pat @k @y @(d + 2 + PSize x) @'[ '(d + 1, a2)] @a2 @g' @c b (\py -> k (px, py)))
      )

-- | The variables of a @rec@ block, as GHC tuples them up.
type RecVars :: Type -> Type -> Constraint
class RecVars k t | t -> k where
  type Vars k t :: Ctx k
  recVars :: t
  consume :: t %1 -> r %1 -> r

instance (Monoidal k, KnownObj (a :: SYN k)) => RecVars k (Term d '[ '(n, a)] a) where
  type Vars k (Term d '[ '(n, a)] a) = '[ '(n, a)]
  recVars = var @n @a
  consume (MkTerm _) r = r

instance (RecVars k x, RecVars k y) => RecVars k (x, y) where
  type Vars k (x, y) = Union (Vars k x) (Vars k y)
  recVars = (recVars, recVars)
  consume (x, y) r = consume x (consume y r)

instance (RecVars k x, RecVars k y, RecVars k z) => RecVars k (x, y, z) where
  type Vars k (x, y, z) = Union (Vars k x) (Vars k (y, z))
  recVars = (recVars, recVars, recVars)
  consume (x, y, z) r = consume x (consume (y, z) r)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w) => RecVars k (x, y, z, w) where
  type Vars k (x, y, z, w) = Union (Vars k x) (Vars k (y, z, w))
  recVars = (recVars, recVars, recVars, recVars)
  consume (x, y, z, w) r = consume x (consume (y, z, w) r)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v) => RecVars k (x, y, z, w, v) where
  type Vars k (x, y, z, w, v) = Union (Vars k x) (Vars k (y, z, w, v))
  recVars = (recVars, recVars, recVars, recVars, recVars)
  consume (x, y, z, w, v) r = consume x (consume (y, z, w, v) r)

instance
  (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v, RecVars k u)
  => RecVars k (x, y, z, w, v, u)
  where
  type Vars k (x, y, z, w, v, u) = Union (Vars k x) (Vars k (y, z, w, v, u))
  recVars = (recVars, recVars, recVars, recVars, recVars, recVars)
  consume (x, y, z, w, v, u) r = consume x (consume (y, z, w, v, u) r)

-- | The end of a @rec@ block: all its variables, as the tensor of their context.
return
  :: forall k t d. (Monoidal k, RecVars k t, KnownCtx (Vars k t)) => t %1 -> Ret t (Term d (Vars k t) (Mul (Vars k t)))
return t = Ret (consume t (MkTerm (ctxOb @(Vars k t))))

-- | A @rec@ block after tracing, from its context without the fed back variables to the variables
-- it passes on.
type Rec :: forall {k}. Nat -> Type -> Ctx k -> Ctx k -> Type
data Rec d t g0 outs where
  Rec :: (Interp (Mul g0) ~> Interp (Mul outs)) %Many -> Rec d t g0 outs

-- | Trace a @rec@ block: the variables it uses before binding them are fed back.
mfix
  :: forall {k} t d (g :: Ctx k)
   . ( TracedMonoidal k
     , RecVars k t
     , Merge (Inter g (Vars k t)) (Minus g (Vars k t))
     , Merge (Inter g (Vars k t)) (Minus (Vars k t) g)
     , Union (Inter g (Vars k t)) (Minus g (Vars k t)) ~ g
     , Union (Inter g (Vars k t)) (Minus (Vars k t) g) ~ Vars k t
     )
  => (t -> Ret t (Term d g (Mul (Vars k t)))) %1 -> Rec d t (Minus g (Vars k t)) (Minus (Vars k t) g)
mfix f = case unRet (f recVars) of
  MkTerm body ->
    withCtxOb @(Inter g (Vars k t))
      ( withCtxOb @(Minus g (Vars k t))
          ( withCtxOb @(Minus (Vars k t) g)
              ( Rec
                  ( coact
                      @Tensor
                      @(~>)
                      @(Interp (Mul (Inter g (Vars k t))))
                      @(Interp (Mul (Minus g (Vars k t))))
                      @(Interp (Mul (Minus (Vars k t) g)))
                      ( merge @(Inter g (Vars k t)) @(Minus (Vars k t) g)
                          . body
                          . unmerge @(Inter g (Vars k t)) @(Minus g (Vars k t))
                      )
                  )
              )
          )
      )

-- | The rest of the @do@ block after a @rec@ block. GHC binds the variables of the block here
-- without linearity, so the context checks see to it that the ones passed on are used once and
-- the fed back ones not at all.
instance
  ( SymMonoidal k
  , RecVars k t
  , t' ~ t
  , cont ~ Term (HeadId (Vars k t) + 1) (CtxOf @k cont) (TyOf @k cont)
  , r ~ Term d (Union (Minus (CtxOf @k cont) outs) g0) (TyOf @k cont)
  , AllIn outs (CtxOf @k cont)
  , NoneIn (Minus (CtxOf @k cont) outs) (Vars k t)
  , Merge (Minus (CtxOf @k cont) outs) g0
  , Merge (Minus (CtxOf @k cont) outs) outs
  , CtxOf @k cont ~ Union (Minus (CtxOf @k cont) outs) outs
  )
  => Bind k (Rec d t (g0 :: Ctx k) outs) t' Many cont r
  where
  Rec h >>= k = case k recVars of
    MkTerm body ->
      MkTerm
        ( body
            . unmerge @(Minus (CtxOf @k cont) outs) @outs
            . (ctxOb @(Minus (CtxOf @k cont) outs) ** h)
            . merge @(Minus (CtxOf @k cont) outs) @g0
        )

-- | GHC's translation of @rec@ refers to @fail@, but pairs of variables always match.
fail :: a
fail = P.error "Proarrow.Tools.SMC.fail: a pattern did not match"

retag :: Term d g a %1 -> Term d' g a
retag (MkTerm f) = MkTerm f

type DepthOf :: Type -> Nat
type family DepthOf t where
  DepthOf (Term d g a) = d

type CtxOf :: forall k. Type -> Ctx k
type family CtxOf t where
  CtxOf (Term d g a) = g

type TyOf :: forall k. Type -> SYN k
type family TyOf t where
  TyOf (Term d g a) = a

type Drop2 :: forall {k}. Ctx k -> Ctx k
type family Drop2 g where
  Drop2 (x ': y ': g) = g

type HeadId :: forall {k}. Ctx k -> Nat
type family HeadId g where
  HeadId ('(n, a) ': g) = n

-- | Every variable of the first context is in the second.
type AllIn :: forall {k}. Ctx k -> Ctx k -> Constraint
type AllIn g h = IsEmpty (Text "Proarrow.Tools.SMC: a variable bound in a rec block is not used") (Minus g h)

-- | No variable of the first context is in the second.
type NoneIn :: forall {k}. Ctx k -> Ctx k -> Constraint
type NoneIn g h =
  IsEmpty (Text "Proarrow.Tools.SMC: a variable fed back in a rec block is also used after it") (Inter g h)

type IsEmpty :: forall {k}. ErrorMessage -> Ctx k -> Constraint
type family IsEmpty msg g where
  IsEmpty msg '[] = ()
  IsEmpty msg g = TypeError msg

-- | The variables of @g@ whose ids are not in @h@.
type Minus :: forall {k}. Ctx k -> Ctx k -> Ctx k
type family Minus g h where
  Minus '[] h = '[]
  Minus g '[] = g
  Minus ('(n, a) ': g) ('(m, b) ': h) = MinusBy (CmpNat n m) ('(n, a) ': g) ('(m, b) ': h)

type MinusBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Ctx k
type family MinusBy o g h where
  MinusBy GT (x ': g) h = x ': Minus g h
  MinusBy EQ (x ': g) (y ': h) = Minus g h
  MinusBy LT g (y ': h) = Minus g h

-- | The variables of @g@ whose ids are in @h@.
type Inter :: forall {k}. Ctx k -> Ctx k -> Ctx k
type Inter g h = Minus g (Minus g h)

-- $
-- The examples below are compiled at @k = 'Data.Kind.Type'@, where the result can be run.

-- | Swap a tensor.
--
-- >>> import Prelude (Bool (..))
-- >>> swapT @Bool @Bool (True, False)
-- (False,True)
swapT :: forall {k} (a :: k) b. (SymMonoidal k, Ob a, Ob b) => a ** b ~> b ** a
swapT = toSMC @(F a :** F b) (\p -> split p (\x y -> y * x))

-- | Apply a function to an argument, both in a tensor.
--
-- >>> import Prelude (Bool (..), not)
-- >>> applyT @Bool @Bool (not, True)
-- False
applyT :: forall {k} (a :: k) b. (Closed k, SymMonoidal k, Ob a, Ob b) => (a ~~> b) ** a ~> b
applyT = toSMC @((F a :-> F b) :** F a) (\p -> split p (\f x -> f $$ x))

-- | Curry the tensor.
--
-- >>> import Prelude (Bool (..))
-- >>> curryT @Bool @Bool True False
-- (True,False)
curryT :: forall {k} (a :: k) b. (Closed k, SymMonoidal k, Ob a, Ob b) => a ~> b ~~> a ** b
curryT = toSMC @(F a) @(F b :-> F a :** F b) (\x -> lam (\y -> x * y))

-- | Rotate a triple, with a nested pattern.
--
-- >>> import Prelude (Bool (..), Int)
-- >>> rotT @Int @Bool @Int ((1, True), 2)
-- ((True,2),1)
rotT :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => a ** b ** c ~> b ** c ** a
rotT = toSMC @(F a :** F b :** F c) \x -> Proarrow.Tools.SMC.do
  ((a, b), c) <- x
  b * c * a

-- | Trace out @u@ with a @rec@ block. In 'Data.Kind.Type' the trace is a lazy fixed point.
--
-- >>> import Prelude (Int, take)
-- >>> traceT @Int @[Int] @[Int] (\(a, u) -> (take 3 u, a : u)) 1
-- [1,1,1]
traceT :: forall {k} (a :: k) b u. (TracedMonoidal k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
traceT h = toSMC @(F a) \a -> Proarrow.Tools.SMC.do
  rec (b, u) <- lift @(F a :** F u) @(F b :** F u) h (a * u)
  b

-- | Trace out @u@ with 'loop'.
--
-- >>> import Prelude (Int, take)
-- >>> loopT @Int @[Int] @[Int] (\(a, u) -> (take 3 u, a : u)) 1
-- [1,1,1]
loopT :: forall {k} (a :: k) b u. (TracedMonoidal k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
loopT h = toSMC @(F a) \a -> loop @(F u) \u -> lift @(F a :** F u) @(F b :** F u) h (a * u)

-- | A trace from the duality alone, so for any compact closed category: feed @u@ in along one
-- end of a new pair and join its new value with the other end.
loopCC :: forall {k} (a :: k) b u. (CompactClosed k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
loopCC h = toSMC @(F a) \a -> Proarrow.Tools.SMC.do
  (u, u') <- produce
  (b, v) <- lift @(F a :** F u) @(F b :** F u) h (a * u)
  () <- annihilate u' v
  b

-- | A snake: create a pair, join its dual with the input, and continue with the other end. By the
-- zigzag law it is the identity.
snakeT :: forall {k} (a :: k). (CompactClosed k, Ob a) => a ~> a
snakeT = toSMC @(F a) \x -> Proarrow.Tools.SMC.do
  (a, a') <- produce
  () <- annihilate a' x
  a

-- | The inverse of 'distribDual': make a pair for @a ** b@, and annihilate the two halves of its
-- plain end with the given duals.
combineDualT :: forall {k} (a :: k) b. (CompactClosed k, Ob a, Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDualT = toSMC @(D (F a) :** D (F b)) @(D (F a :** F b)) \x -> Proarrow.Tools.SMC.do
  (da, db) <- x
  (ab, ab') <- produce
  (a, b) <- ab
  () <- annihilate da a
  () <- annihilate db b
  ab'
