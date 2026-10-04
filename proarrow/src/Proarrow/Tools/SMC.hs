{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | A HOAS front end for building morphisms in any symmetric monoidal category, the linear
-- counterpart of "Proarrow.Tools.CCC", which grows with the structure of the target: traces,
-- duals, additives, and the polarised System L reading of inputs and outputs in a dialogue
-- category. Each variable is used exactly once: the functions on terms
-- are linear, so GHC's linear types check that every variable is used once, and a 'Term' is
-- indexed by its context, which is exactly the variables it uses. So a variable is the identity
-- on its own type, and no copying or discarding is ever generated. Terms with disjoint contexts
-- combine by merging the contexts, which only reorders wires. Functions on terms need
-- @LinearTypes@ and linear arrows, e.g. @'Term' d g a %1 -> 'Term' d g b@.
--
-- Types are 'SYN' expressions, interpreted in the target category by 'Interp'. Their tensor is a
-- constructor, so a pattern can take a term's type apart, which the target's own @**@, a type
-- family, would not allow.
--
-- Every variable has an id, the number of binders around it, and a context lists its variables
-- by descending id. Merging compares ids, so it only reduces where the depths are known, which is
-- the case for terms built directly inside 'toSMC'. A reusable piece that binds variables of its
-- own is compiled on its own: with 'closed' when it has no inputs, and used through 'call'
-- otherwise.
--
-- The module also provides @do@ notation, for use with @QualifiedDo@, and with @RecursiveDo@ a
-- @rec@ block traces, which needs a traced monoidal category. Composition in the Int construction
-- ("Proarrow.Category.Instance.IntConstruction") uses both: the two morphisms run side by side,
-- and the wires each needs from the other are fed back.
--
-- > import Proarrow.Tools.SMC (SYN (..), lift, toSMC, (**))
-- > import Proarrow.Tools.SMC qualified as SMC
-- >
-- > Int @bp @bm @cp @cm f . Int @ap @am g =
-- >   Int $ toSMC @(F ap :** F cm) \x -> SMC.do
-- >     let g' = lift @(F ap :** F bm) @(F am :** F bp) g
-- >         f' = lift @(F bp :** F cm) @(F bm :** F cp) f
-- >     (ap, cm) <- x
-- >     rec ((am, bp), (bm, cp)) <- g' (ap ** bm) ** f' (bp ** cm)
-- >     am ** cp
--
-- A bind takes its right hand side apart with a pattern, see /Patterns/ below. In a @rec@ block,
-- the variables that are used before they are bound, @bm@ and @bp@ above, are fed back, and the others are passed on to the rest of
-- the block. GHC's translation of @rec@ passes every variable of the block to its end again,
-- including the ones a later statement of the block already used, so only such blocks work where
-- no statement uses a variable bound by an earlier one. A block of a single statement always
-- qualifies, and a nested pattern lets one statement bind everything, as above. 'loop' traces
-- without GHC's translation, so it has neither restriction, but the type of the fed back variable
-- has to be given.
--
-- The module is inspired by Bernardy and Spiwack,
-- [Evaluating Linear Functions to Symmetric Monoidal Categories](https://arxiv.org/abs/2103.06195), whose
-- @P k r a@ ports correspond to 'Term', @encode@ to 'lift', @decode@ to 'toSMC', @(!:)@ to
-- '(**)' and @split@ to 'split'. Unlike their implementation, it keeps the context thinned instead
-- of computing in the cartesian structure and arguing afterwards that the result is monoidal.
module Proarrow.Tools.SMC
  ( -- * Types
    SYN (..)
  , Interp
  , KnownObj (..)
  , synOb

    -- * Patterns
    -- $patterns

    -- * Terms

    -- ** Symmetric monoidal categories
  , Term (..)
  , toSMC
  , lift
  , call
  , closed
  , unit
  , (**)
  , split
  , Tuple (..)
  , TupleCtx
  , TupleDepth
  , recast

    -- ** Closed categories
  , lam
  , (!)

    -- ** CopyDiscard / Comonoids
  , dup
  , drop

    -- ** Traced monoidal categories
  , loop

    -- * Inputs and outputs
    -- $inout

    -- ** Dialogue categories
  , Up
  , Consumer
  , Command
  , type (:##)
  , cont
  , cut
  , (|>)
  , ret
  , thunk
  , force

    -- ** Isomix categories
  , annihilate

    -- ** *-autonomous categories
  , classical

    -- ** Compact closed categories
  , produce

    -- * Additives
    -- $additives
  , with
  , exl
  , exr
  , absorb
  , inl
  , inr
  , caseOf
  , absurd

    -- * Contexts
  , Ctx
  , Mul
  , KnownCtx
  , ctxOb
  , withCtxOb
  , Union
  , Merge (..)
  , snoc
  , push2

    -- * Do notation
  , (>>=)
  , return
  , mfix
  , fail
  , Bind
  , BindPat
  , Binds
  , Pat
  , Ret
  , Rec
  , RecVars

    -- * Examples
  , swapT
  , rotT
  , applyT
  , curryT
  , traceT
  , loopT
  , loopCC
  , snakeT
  , snakeDualT
  , combineDualT
  , dniT
  , dneT
  , bindT
  , contraT
  , parSwapT
  , weakDistT
  , bothWaysT
  , distT
  , swapEitherT
  ) where

import Data.Kind (Constraint, Type)
import GHC.Exts (Multiplicity (..))
import GHC.TypeLits (ErrorMessage (..), TypeError)
import GHC.TypeNats (CmpNat, Nat, type (+))
import Prelude (Ordering (..), type (~))
import Prelude qualified as P

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , SymMonoidal (..)
  , Tensor
  , associator'
  , associatorInv'
  )
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..), Par, bindDual, dualityCounitSA)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Monoidal.IsoMix (IsoMix (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal, trace)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object (Obj)

infixl 7 **
infixl 1 |>
infixl 8 !
infixl 7 :**
infixl 7 :##
infixl 6 :&&
infixl 6 :||
infixr 5 :->

-- | Type expressions over the objects of @k@: an object of @k@, the unit, the tensor, the
-- internal hom and the negation, and the additives: the product and its unit 'Top', and the
-- coproduct and its unit 'Zero'.
--
-- The negation gives the types a polarity: a type is negative when it is a 'Not', and positive
-- otherwise. A term of a positive type is a value, and a term of a negative type is a consumer
-- of what it negates. 'Up' shifts a positive type to a negative one, and 'Dn' a negative type to
-- a positive one, standing for the same object: a term of @'Dn' n@ is a stored term of @n@.
type data SYN k
  = F k
  | I
  | SYN k :** SYN k
  | SYN k :-> SYN k
  | Not (SYN k)
  | Dn (SYN k)
  | SYN k :&& SYN k
  | Top
  | SYN k :|| SYN k
  | Zero

-- | The object of @k@ a type expression stands for.
type Interp :: forall {k}. SYN k -> k
type family Interp s where
  Interp (F a) = a
  Interp I = Unit
  Interp (a :** b) = Interp a ** Interp b
  Interp (a :-> b) = Interp a ~~> Interp b
  Interp (Not a) = Dual (Interp a)
  Interp (Dn a) = Interp a
  Interp (a :&& b) = Interp a && Interp b
  Interp Top = TerminalObject
  Interp (a :|| b) = Interp a || Interp b
  Interp Zero = InitialObject

-- | Type expressions whose 'Interp' is an object, given that their leaves are.
type KnownObj :: forall {k}. SYN k -> Constraint
class (CategoryOf k) => KnownObj (s :: SYN k) where
  withSynOb :: ((Ob (Interp s)) => r) -> r

instance (CategoryOf k, Ob (a :: k)) => KnownObj (F a) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

instance (Monoidal k) => KnownObj (I :: SYN k) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

instance (Monoidal k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :** b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withOb2 @k @(Interp a) @(Interp b) r))

instance (Closed k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :-> b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withObExp @k @(Interp a) @(Interp b) r))

instance (KnownObj (a :: SYN k)) => KnownObj (Dn a) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a r

instance (Dialogue k, KnownObj (a :: SYN k)) => KnownObj (Not a) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withObDual @k @(Interp a) r)

instance (HasBinaryProducts k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :&& b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withObProd @k @(Interp a) @(Interp b) r))

instance (HasTerminalObject k) => KnownObj (Top :: SYN k) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

instance (HasBinaryCoproducts k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :|| b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withObCoprod @k @(Interp a) @(Interp b) r))

instance (HasInitialObject k) => KnownObj (Zero :: SYN k) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

-- | The identity on the object a type expression stands for.
{-# INLINE synOb #-}
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
  MkTerm :: (Interp (Mul g) ~> Interp a) -> Term d g a

-- | A context that is known to be empty or not, all the way down.
type KnownCtx :: forall {k}. Ctx k -> Constraint
class KnownCtx (g :: Ctx k) where
  -- | Case analysis on the context, which is what lets @'Mul' ('(n, a) ': g)@ reduce.
  ctxCase :: ((g ~ '[]) => r) -> (forall n a g'. (g ~ ('(n, a) ': g'), KnownObj a, KnownCtx g') => r) -> r

  -- | The tensor of a context is an object. A method rather than a function over 'ctxCase', so that
  -- at a known context it is not recursive and can be inlined.
  withCtxOb :: (Monoidal k) => ((Ob (Interp (Mul g))) => r) -> r

instance KnownCtx ('[] :: Ctx k) where
  {-# INLINE ctxCase #-}
  {-# INLINE withCtxOb #-}
  ctxCase e _ = e
  withCtxOb r = r

instance (KnownObj a, KnownCtx g) => KnownCtx ('(n, a) ': g) where
  {-# INLINE ctxCase #-}
  {-# INLINE withCtxOb #-}
  ctxCase _ c = c
  withCtxOb r = ctxCase @g (withSynOb @a r) (withCtxOb @g (withSynOb @a (withOb2 @_ @(Interp (Mul g)) @(Interp a) r)))

-- | The identity on the tensor of a context.
{-# INLINE ctxOb #-}
ctxOb :: forall {k} (g :: Ctx k). (Monoidal k, KnownCtx g) => Obj (Interp (Mul g))
ctxOb = withCtxOb @g (obj @(Interp (Mul g)))

-- | A new variable on the right of a context: a unitor if the context was empty, and nothing
-- otherwise.
{-# INLINE snoc #-}
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
  {-# INLINE merge #-}
  {-# INLINE unmerge #-}
  merge = withCtxOb @g2 leftUnitorInv
  unmerge = withCtxOb @g2 leftUnitor

instance (Monoidal k, KnownCtx ('(n, a) ': g1)) => Merge ('(n, a) ': g1 :: Ctx k) '[] where
  {-# INLINE merge #-}
  {-# INLINE unmerge #-}
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
  {-# INLINE merge #-}
  {-# INLINE unmerge #-}
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
  {-# INLINE mergeBy #-}
  {-# INLINE unmergeBy #-}
  mergeBy =
    withCtxOb @('(m, b) ': g2)
      ( withSynOb @a
          ( ctxCase @g1
              (swap @k @(Interp (Mul ('(m, b) ': g2))) @(Interp a))
              ( associatorInv' (ctxOb @g1) (synOb @a) (ctxOb @('(m, b) ': g2))
                  . (ctxOb @g1 M.** swap @k @(Interp (Mul ('(m, b) ': g2))) @(Interp a))
                  . associator' (ctxOb @g1) (ctxOb @('(m, b) ': g2)) (synOb @a)
                  . (merge @g1 @('(m, b) ': g2) M.** synOb @a)
              )
          )
      )
  unmergeBy =
    withCtxOb @('(m, b) ': g2)
      ( withSynOb @a
          ( ctxCase @g1
              (swap @k @(Interp a) @(Interp (Mul ('(m, b) ': g2))))
              ( (unmerge @g1 @('(m, b) ': g2) M.** synOb @a)
                  . associatorInv' (ctxOb @g1) (ctxOb @('(m, b) ': g2)) (synOb @a)
                  . (ctxOb @g1 M.** swap @k @(Interp a) @(Interp (Mul ('(m, b) ': g2))))
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
  {-# INLINE mergeBy #-}
  {-# INLINE unmergeBy #-}
  mergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( associator' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
          . (merge @('(n, a) ': g1) @g2 M.** synOb @b)
      )
  unmergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( (unmerge @('(n, a) ': g1) @g2 M.** synOb @b)
          . associatorInv' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
      )

-- | The variable with id @n@: the identity on its type.
{-# INLINE var #-}
var :: forall {k} n (a :: SYN k) d. (CategoryOf k, KnownObj a) => Term d '[ '(n, a)] a
var = withSynOb @a (MkTerm (obj @(Interp a)))

-- $patterns
-- Wherever a function on terms receives an input, that is the function given to 'toSMC', 'lam',
-- 'loop' and 'cont', the alternatives of 'with' and 'caseOf', and the left of a bind in @do@
-- notation, the input arrives through a pattern: a variable, @()@, or a tuple of patterns. A
-- variable stands for the whole input, whatever its type, and must be used exactly once. @()@
-- matches the unit 'I'. A pair matches a tensor @a ':**' b@ and binds its two sides, and a triple
-- or quadruple is pairs nested to the left, as @a ':**' b ':**' c@ is. At a computation,
-- @'Up' (a ':**' b)@ or @'Up' 'I'@, a pair or @()@ pattern runs the computation and matches its
-- value, so the rest of the block must be of a negative type; a variable at a computation only
-- names it.
--
-- Tuples build terms as well, the mirror image of taking them apart: 'tuple', and 'ret' of a
-- tuple, make a pair at a tensor into '(**)' of its parts and a pair at a computation into the
-- computation of the pair.

-- | Compile a function on terms to a morphism. The function receives the input through a pattern
-- (see /Patterns/), so @()@ compiles a term without inputs and a tuple takes a tensor apart.
{-# INLINE toSMC #-}
toSMC
  :: forall {k} (a :: SYN k) b t cont
   . (Monoidal k, Binds t 0 a cont '[] b)
  => (t %1 -> cont)
  -> Interp a ~> Interp b
toSMC k = case bound @0 @'[] @a @b k of MkTerm f -> f

-- | Copy a term whose type is a comonoid, in "Proarrow.Tools.SMC": @(x1, x2) <- dup x@.
{-# INLINE dup #-}
dup :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s %1 -> Term d g (s :** s)
dup = lift @s @(s :** s) comult

-- | Discard a term whose type is a comonoid, in "Proarrow.Tools.SMC": @() <- drop x@.
{-# INLINE drop #-}
drop :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s %1 -> Term d g I
drop = lift @s @I counit

-- | Lift a morphism of the target category to a function on terms.
{-# INLINE lift #-}
lift :: forall {k} (a :: SYN k) b d g. (CategoryOf k) => (Interp a ~> Interp b) -> Term d g a %1 -> Term d g b
lift f (MkTerm t) = MkTerm (f . t)

-- | A term without variables, written at depth 0, for use at any depth. A reusable piece that
-- has no inputs but binds variables of its own is defined with it.
{-# INLINE closed #-}
closed :: forall {k} (a :: SYN k) d. Term 0 '[] a -> Term d '[] a
closed t = recast t

-- | Use a function on terms inside another term, compiled on its own with 'toSMC', so that its
-- argument is a pattern too. This is how a reusable piece that binds variables of its own is used,
-- and unlike 'lift' of the compiled morphism it needs no type annotations.
{-# INLINE call #-}
call
  :: forall {k} (a :: SYN k) b d g t cont
   . (Monoidal k, Binds t 0 a cont '[] b)
  => (t %1 -> cont)
  -> Term d g a
  %1 -> Term d g b
call f = lift @a @b (toSMC @a @b f)

-- | Two terms side by side. Their contexts must be disjoint.
{-# INLINE (**) #-}
(**)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Monoidal k, Merge g1 g2)
  => Term d g1 a %1 -> Term d g2 b %1 -> Term d (Union g1 g2) (a :** b)
MkTerm f ** MkTerm g = MkTerm ((f M.** g) . merge @g1 @g2)

-- | Two new variables @(n, a)@ and @(m, b)@ on the right of the context @r@, for 'split'. When @r@
-- is empty the pair is the whole context.
{-# INLINE push2 #-}
push2
  :: forall {k} r n (a :: SYN k) m b g
   . (Monoidal k, KnownObj a, KnownObj b, Merge r g)
  => (Interp (Mul g) ~> Interp a ** Interp b)
  -> Interp (Mul (Union r g)) ~> Interp (Mul ('(m, b) ': '(n, a) ': r))
push2 p =
  ctxCase @r
    p
    (associatorInv' (ctxOb @r) (synOb @a) (synOb @b) . (ctxOb @r M.** p) . merge @r @g)

-- | Take a tensor apart: the continuation gets a variable for each side and must use both.
{-# INLINE split #-}
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
{-# INLINE unit #-}
unit :: forall {k} d. (Monoidal k) => Term d ('[] :: Ctx k) I
unit = MkTerm id

-- | A function: the body receives the argument through a pattern (see /Patterns/). This needs the
-- category to be closed.
{-# INLINE lam #-}
lam
  :: forall {k} d r (a :: SYN k) b t cont
   . (Closed k, Binds t d a cont r b)
  => (t %1 -> cont)
  %1 -> Term d r (a :-> b)
lam k = case bound @d @r @a @b k of
  MkTerm body -> withCtxOb @r (withSynOb @a (MkTerm (curry @k @(Interp (Mul r)) @(Interp a) (body . snoc @d @a @r))))

-- | The body of a binder, with the pattern taking apart its new variable: what 'toSMC', 'lam',
-- 'loop' and 'cont' share, and the binds of a computation through 'runUp'.
{-# INLINE bound #-}
bound
  :: forall {k} d r (a :: SYN k) b t cont
   . (Binds t d a cont r b)
  => (t %1 -> cont)
  %1 -> Term (d + 1) ('(d, a) ': r) b
bound k = bindPat (var @d @a @(d + 1)) k

-- | Trace: the body receives the value fed back through a pattern (see /Patterns/), and returns
-- it again next to the result. This needs the category to be traced.
{-# INLINE loop #-}
loop
  :: forall {k} (u :: SYN k) b d r t cont
   . (TracedMonoidal k, KnownObj b, Binds t d u cont r (b :** u))
  => (t %1 -> cont)
  %1 -> Term d r b
loop k = case bound @d @r @u @(b :** u) k of
  MkTerm body ->
    withCtxOb @r
      (withSynOb @u (withSynOb @b (MkTerm (trace @(~>) @(Interp u) @(Interp (Mul r)) @(Interp b) (body . snoc @d @u @r)))))

-- | A new pair of wires, a variable and its dual, from nothing: the unit of the duality. This
-- needs the category to be compact closed.
{-# INLINE produce #-}
produce :: forall {k} (a :: SYN k) d. (CompactClosed k, KnownObj a) => Term d '[] (a :** Not a)
produce = withSynOb @a (MkTerm (dualityUnit @k @(Interp a)))

-- | Join a dual and its wire into nothing: the counit of the duality, which an isomix category
-- has.
{-# INLINE annihilate #-}
annihilate
  :: forall {k} (a :: SYN k) d g1 g2
   . (IsoMix k, KnownObj a, Merge g1 g2)
  => Consumer d g1 a %1 -> Term d g2 a %1 -> Term d (Union g1 g2) I
annihilate x y = lift @(Not a :** a) @I (withSynOb @a (dualityCounit @k @(Interp a))) (x ** y)

-- $inout
-- In a dialogue category, one with a tensorial negation 'Dual', a term of @'Not' a@ consumes an
-- @a@: an output, seen as an input. Terms then read as in System L, the μμ̃-calculus, which treats
-- the two alike. A 'Term' of @a@ produces an @a@ and a 'Consumer' of @a@, a term of @'Not' a@,
-- consumes one; 'cut', or @t '|>' k@, is the two meeting, a 'Command', a term of @'Not' 'I'@; and
-- 'cont' is the one binder, which receives an @a@ and runs a command with it, whether that @a@ is
-- an input or the consumer of an output.
--
-- The types have a polarity: @'Not' a@ is negative, everything else positive. A term of a negative
-- type is given its consumer, so binding an output of a positive type @a@ with 'cont' gives
-- @'Up' a = 'Not' ('Not' a)@, a computation that will produce an @a@, and 'ret' makes a value into
-- the computation that produces it. In @do@ notation, binding a computation runs it, with the rest
-- of the block, which must be negative, as what happens next; this is where terms get an
-- evaluation order, which a symmetric monoidal category does not have by itself. 'Dn' is the
-- shift the other way, the same object at positive polarity: 'thunk' and 'force' are identities
-- on the morphism, and a bind names a @'Dn' ('Up' a)@ instead of running it. Patterns and tuples
-- at a computation are described under /Patterns/.
--
-- More structure in the category adds to this. In an isomix category a consumer and its value
-- join into the unit itself rather than into @'Not' 'I'@ ('annihilate'). In a *-autonomous
-- category the negation is an involution, so a computation is its value again ('classical') and
-- the polarities collapse. In a compact closed category a value and its consumer can also be
-- created from nothing ('produce'), which gives traces and bends wires back on themselves.

-- | The shift of a positive type to a negative one: a computation that produces an @a@. A term of
-- it is a consumer of consumers of @a@, so in a category with @'Dual' a = a ~~> r@ it is the
-- continuation passing type @(a -> r) -> r@.
type Up :: forall {k}. SYN k -> SYN k
type Up a = Not (Not a)

-- | A consumer of @a@: a term of its negation.
type Consumer :: forall {k}. Nat -> Ctx k -> SYN k -> Type
type Consumer d g a = Term d g (Not a)

-- | A producer and a consumer meeting: a term of the unit of par.
type Command :: forall {k}. Nat -> Ctx k -> Type
type Command d g = Term d g (Not I)

-- | Par, the negation of the tensor of the negations, interpreted as 'Proarrow.Category.Monoidal.Dialogue.Par'.
type (:##) :: forall {k}. SYN k -> SYN k -> SYN k
type a :## b = Not (Not a :** Not b)

-- | A consumer meets a producer: @cut k t@ gives @t@ to @k@, like applying a continuation.
{-# INLINE cut #-}
cut
  :: forall {k} (a :: SYN k) d g1 g2
   . (Dialogue k, KnownObj a, Merge g1 g2)
  => Consumer d g1 a %1 -> Term d g2 a %1 -> Command d (Union g1 g2)
cut x y = lift @(Not a :** a) @(Not I) (withSynOb @a (dualityCounitSA @(Interp a))) (x ** y)

-- | 'cut' with the producer first, as System L writes @⟨t | k⟩@: @t |> k@ sends @t@ into @k@.
{-# INLINE (|>) #-}
(|>)
  :: forall {k} (a :: SYN k) d g1 g2
   . (Dialogue k, KnownObj a, Merge g2 g1)
  => Term d g1 a %1 -> Consumer d g2 a %1 -> Command d (Union g2 g1)
t |> k = cut k t

-- | The binder of System L. @cont \\x -> c@ is a term of @'Not' a@: it receives an @a@ through the
-- pattern @x@ (see /Patterns/) and runs the command @c@ with it.
--
-- What that @a@ is depends on how the result is used. As a 'Consumer' of @a@, the @a@ is an input
-- and @cont@ is μ̃: the seller in a shop receives the order, @cont \\(name, card, replyTo) -> …@. As
-- a term of the negative type @'Not' a@ in its own right, the @a@ is the consumer of an output and
-- @cont@ is μ, Haskell's @callCC@: a computation @'Up' b@ receives the consumer of its result,
-- @cont \\k -> … |> k@; a par @b ':##' c@ receives a consumer for each side, @cont \\(kb, kc) -> …@;
-- and a command, @'Not' 'I'@, receives nothing, @cont \\() -> …@. A consumer of a par is a
-- computation, which a nested pair pattern runs to get at the consumers of its sides.
{-# INLINE cont #-}
cont
  :: forall {k} d r (a :: SYN k) t cont
   . (Dialogue k, Binds t d a cont r (Not I))
  => (t %1 -> cont)
  %1 -> Term d r (Not a)
cont k = case bound @d @r @a @(Not I) k of
  MkTerm body ->
    withCtxOb @r
      ( withSynOb @a
          ( MkTerm
              ( dual (rightUnitorInv @k @(Interp a))
                  . linDist @k @(Interp (Mul r)) @(Interp a) @Unit (body . snoc @d @a @r)
              )
          )
      )

-- | Run a computation against the rest of a block. The body is what the rest does with the value,
-- given the context @r@; it becomes a consumer of the computation, whose context @g@ joins. What
-- the binds of a computation share, the counterpart of 'bound'.
{-# INLINE runUp #-}
runUp
  :: forall {k} d g r (a :: SYN k) y
   . (Dialogue k, KnownObj a, KnownObj y, Merge g r)
  => Term d g (Up a)
  %1 -> (Interp (Mul r) ** Interp a ~> Interp (Not y))
  -> Term d (Union g r) (Not y)
runUp (MkTerm m) body =
  withCtxOb @r
    ( withSynOb @a
        ( withSynOb @y
            ( MkTerm
                ( bindDual @(Interp (Mul r)) @(Interp a) @(Interp y) body
                    . (m M.** obj @(Interp (Mul r)))
                    . merge @g @r
                )
            )
        )
    )

-- | A value as the computation that produces it: double negation introduction, and the return of
-- a @do@ block in the continuation reading. It also reads as a producer of @a@ handed over as a
-- consumer of @'Not' a@. The value can be given as a 'Tuple' of terms, built by the type expected.
{-# INLINE ret #-}
ret
  :: forall {k} (a :: SYN k) t
   . (Dialogue k, KnownObj a, Tuple k t a)
  => t %1 -> Term (TupleDepth t) (TupleCtx k t) (Up a)
ret t = withSynOb @a (lift @a @(Up a) (doubleNegInv @k @(Interp a))) (tuple @k @t @a t)

-- | A term built from a tuple of terms, by the type it is expected to have: a term is itself, a
-- pair at a tensor is the tensor of its parts, and a pair at a computation @'Up' a@ is the
-- computation of the pair at @a@. A triple or quadruple stands for pairs nested to the left, as in
-- patterns. The parts must be at the same depth, and their contexts are merged.
type Tuple :: forall k -> Type -> SYN k -> Constraint
class Tuple k t a where
  tuple :: t %1 -> Term (TupleDepth t) (TupleCtx k t) a

-- | The context of a tuple of terms: the union of the contexts of its parts.
type TupleCtx :: forall k -> Type -> Ctx k
type family TupleCtx k t where
  TupleCtx k (x, y) = Union (TupleCtx k x) (TupleCtx k y)
  TupleCtx k (x, y, z) = TupleCtx k ((x, y), z)
  TupleCtx k (w, x, y, z) = TupleCtx k (((w, x), y), z)
  TupleCtx k t = CtxOf @k t

-- | The depth of a tuple of terms: that of its first part.
type TupleDepth :: Type -> Nat
type family TupleDepth t where
  TupleDepth (x, y) = TupleDepth x
  TupleDepth (x, y, z) = TupleDepth x
  TupleDepth (w, x, y, z) = TupleDepth w
  TupleDepth t = DepthOf t

-- The generic instances are incoherent, as for patterns: a term's type is often still unknown when
-- the instance is chosen, and a pair defaults to a tensor until its type is known to be an 'Up'.

-- | A term is itself.
instance {-# INCOHERENT #-} (t ~ Term d g a) => Tuple k t a where
  {-# INLINE tuple #-}
  tuple t = t

-- | A pair at a tensor is the tensor of its parts.
instance
  {-# INCOHERENT #-}
  ( Monoidal k
  , a ~ (a1 :** a2)
  , Tuple k x a1
  , Tuple k y a2
  , TupleDepth y ~ TupleDepth x
  , Merge (TupleCtx k x) (TupleCtx k y)
  )
  => Tuple k (x, y) (a :: SYN k)
  where
  {-# INLINE tuple #-}
  tuple (x, y) = tuple @k @x @a1 x ** tuple @k @y @a2 y

-- | A pair at a computation is the computation of the pair at the value.
instance (Dialogue k, KnownObj a, Tuple k (x, y) a) => Tuple k (x, y) (Not (Not a) :: SYN k) where
  {-# INLINE tuple #-}
  tuple p = ret @a p

instance (Tuple k ((x, y), z) a) => Tuple k (x, y, z) a where
  {-# INLINE tuple #-}
  tuple (x, y, z) = tuple @k @((x, y), z) @a ((x, y), z)

instance (Tuple k (((w, x), y), z) a) => Tuple k (w, x, y, z) a where
  {-# INLINE tuple #-}
  tuple (w, x, y, z) = tuple @k @(((w, x), y), z) @a (((w, x), y), z)

-- | The same morphism at another type expression for the same object, and at any depth: between
-- @'F' (a '**' b)@ and @'F' a ':**' 'F' b@, say, so that a pattern can take it apart, or between a
-- type and its 'Dn'. The polarity may change, the morphism does not.
{-# INLINE recast #-}
recast :: forall {k} (a :: SYN k) b d d' g. (Interp a ~ Interp b) => Term d g a %1 -> Term d' g b
recast (MkTerm f) = MkTerm f

-- | Store a term of a negative type as a value: the same morphism at the positive type @'Dn' n@,
-- which a bind names instead of running. This is call by push value's @thunk@, 'recast' to 'Dn'.
{-# INLINE thunk #-}
thunk :: forall {k} (n :: SYN k) d g. Term d g n %1 -> Term d g (Dn n)
thunk = recast

-- | A stored term at its negative type again, where a bind runs it. This is call by push value's
-- @force@, 'recast' from 'Dn'.
{-# INLINE force #-}
force :: forall {k} (n :: SYN k) d g. Term d g (Dn n) %1 -> Term d g n
force = recast

-- | A computation as its value again: double negation elimination, which only a *-autonomous
-- category has. There every type is equivalent to its shift, so the polarities collapse.
{-# INLINE classical #-}
classical :: forall {k} (a :: SYN k) d g. (StarAutonomous k, KnownObj a) => Term d g (Up a) %1 -> Term d g a
classical = withSynOb @a (lift @(Up a) @a (doubleNeg @k @(Interp a)))

-- $additives
-- The additives share their context between alternatives, of which only one is used. Terms that
-- share variables can't both be written in a linear function, so the alternatives are functions of
-- their own, compiled with 'toSMC' like the argument of 'call', and what they share is passed in as
-- one term.

-- | Both of two alternatives on the same input: the product. Each alternative receives the input
-- through a pattern (see /Patterns/). This needs products.
{-# INLINE with #-}
with
  :: forall {k} (s :: SYN k) a b d g t1 cont1 t2 cont2
   . (Monoidal k, HasBinaryProducts k, Binds t1 0 s cont1 '[] a, Binds t2 0 s cont2 '[] b)
  => (t1 %1 -> cont1)
  -> (t2 %1 -> cont2)
  -> Term d g s
  %1 -> Term d g (a :&& b)
with f h = lift @s @(a :&& b) (toSMC @s @a f &&& toSMC @s @b h)

-- | The first alternative of a product.
{-# INLINE exl #-}
exl
  :: forall {k} (a :: SYN k) b d g. (HasBinaryProducts k, KnownObj a, KnownObj b) => Term d g (a :&& b) %1 -> Term d g a
exl = lift @(a :&& b) @a (withSynOb @a (withSynOb @b (fst @k @(Interp a) @(Interp b))))

-- | The second alternative of a product.
{-# INLINE exr #-}
exr
  :: forall {k} (a :: SYN k) b d g. (HasBinaryProducts k, KnownObj a, KnownObj b) => Term d g (a :&& b) %1 -> Term d g b
exr = lift @(a :&& b) @b (withSynOb @a (withSynOb @b (snd @k @(Interp a) @(Interp b))))

-- | Use up a term into the unit of the product.
{-# INLINE absorb #-}
absorb :: forall {k} (s :: SYN k) d g. (HasTerminalObject k, KnownObj s) => Term d g s %1 -> Term d g Top
absorb = lift @s @Top (withSynOb @s (terminate @k @(Interp s)))

-- | The left injection into a coproduct.
{-# INLINE inl #-}
inl
  :: forall {k} (a :: SYN k) b d g
   . (HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => Term d g a %1 -> Term d g (a :|| b)
inl = lift @a @(a :|| b) (withSynOb @a (withSynOb @b (lft @k @(Interp a) @(Interp b))))

-- | The right injection into a coproduct.
{-# INLINE inr #-}
inr
  :: forall {k} (a :: SYN k) b d g
   . (HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => Term d g b %1 -> Term d g (a :|| b)
inr = lift @b @(a :|| b) (withSynOb @a (withSynOb @b (rgt @k @(Interp a) @(Interp b))))

-- | Case analysis on a coproduct, given first a term to share between the branches. Both branches
-- receive the pair of the shared term and the contents of their alternative through a pattern
-- (see /Patterns/). This needs the tensor to distribute over the coproduct.
{-# INLINE caseOf #-}
caseOf
  :: forall {k} (s :: SYN k) a b c d g1 g2 t1 cont1 t2 cont2
   . ( Distributive k
     , KnownObj s
     , KnownObj a
     , KnownObj b
     , Merge g1 g2
     , Binds t1 0 (s :** a) cont1 '[] c
     , Binds t2 0 (s :** b) cont2 '[] c
     )
  => Term d g1 s
  %1 -> Term d g2 (a :|| b)
  %1 -> (t1 %1 -> cont1)
  -> (t2 %1 -> cont2)
  -> Term d (Union g1 g2) c
caseOf e x f h =
  lift @(s :** (a :|| b)) @c
    ( withSynOb @s
        ( withSynOb @a
            ( withSynOb @b
                ( (toSMC @(s :** a) @c f ||| toSMC @(s :** b) @c h)
                    . distL @k @(Interp s) @(Interp a) @(Interp b)
                )
            )
        )
    )
    (e ** x)

-- | There is no term of 'Zero', so from one, together with the rest of the context, anything
-- follows.
{-# INLINE absurd #-}
absurd
  :: forall {k} (s :: SYN k) c d g1 g2
   . (Distributive k, KnownObj s, KnownObj c, Merge g1 g2)
  => Term d g1 s %1 -> Term d g2 Zero %1 -> Term d (Union g1 g2) c
absurd e z = lift @(s :** Zero) @c (withSynOb @s (withSynOb @c (initiate @k @(Interp c) . absorbL @k @(Interp s)))) (e ** z)

-- | Function application. The function and its argument must have disjoint contexts.
{-# INLINE (!) #-}
(!)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Closed k, KnownObj a, KnownObj b, Merge g1 g2)
  => Term d g1 (a :-> b) %1 -> Term d g2 a %1 -> Term d (Union g1 g2) b
MkTerm f ! MkTerm x =
  withSynOb @a (withSynOb @b (MkTerm (apply @k @(Interp a) @(Interp b) . (f M.** x) . merge @g1 @g2)))

-- Do notation

-- | The pattern @t@ of a binder: it takes apart the variable @(n, a)@, and the binder's body
-- @cont@ then gives a term at depth @n + 1@ with type @b@, whose context is that variable and @g@.
-- Both the variable's type and the rest of the context must be known.
type Binds :: forall k. Type -> Nat -> SYN k -> Type -> Ctx k -> SYN k -> Constraint
type Binds @k t n a cont g b =
  (KnownObj a, KnownCtx g, BindPat k (Term (n + 1) '[ '(n, a)] a) t cont (Term (n + 1) ('(n, a) ': g) b))

-- | A bind in a @do@ block: a term taken apart by a pattern, or the variables of a @rec@ block.
-- The multiplicity @p@ of the continuation depends only on the right hand side @m@, since GHC
-- needs it before it knows the rest.
type Bind :: Type -> Type -> Type -> Multiplicity -> Type -> Type -> Constraint
class Bind k m t p cont r | m -> k p where
  -- | Bind the right hand side to the pattern of the continuation.
  (>>=) :: m %1 -> (t %p -> cont) %1 -> r

-- | A term on the right hand side is taken apart by the pattern. Incoherent, so that it is chosen
-- as soon as the right hand side is known, unless the right hand side is a computation.
instance {-# INCOHERENT #-} (BindPat k (Term d g a) t cont r) => Bind k (Term d g (a :: SYN k)) t One cont r where
  {-# INLINE (>>=) #-}
  (>>=) = bindPat

-- | A computation on the right hand side runs first, and the rest of the block is negative.
instance
  ( Dialogue k
  , KnownObj y
  , Merge g r
  , TyOf @k cont ~ Not y
  , Binds t d a cont r (Not y)
  , r' ~ Term d (Union g r) (Not y)
  )
  => Bind k (Term d g (Not (Not a))) t One cont r'
  where
  {-# INLINE (>>=) #-}
  m >>= k = case bound @d @r @a @(Not y) k of
    MkTerm body -> runUp @d @g @r @a @y m (body . snoc @d @a @r)

-- | A term on the right hand side taken apart by the pattern of the continuation. The types of the
-- continuation and the result are matched with equalities, so that the instance is chosen as soon
-- as the right hand side is known.
type BindPat :: Type -> Type -> Type -> Type -> Type -> Constraint
class BindPat k m t cont r | m -> k where
  bindPat :: m %1 -> (t %1 -> cont) %1 -> r

instance
  ( cont ~ Term (d + PSize t) (CtxOf @k cont) (TyOf @k cont)
  , r ~ Term d (PCtx t d g a (CtxOf @k cont)) (TyOf @k cont)
  , Pat k t d g a (CtxOf @k cont) (TyOf @k cont)
  )
  => BindPat k (Term d g (a :: SYN k)) t cont r
  where
  {-# INLINE bindPat #-}
  bindPat = pat @k @t @d @g @a @(CtxOf @k cont) @(TyOf @k cont)

-- | The statement of a @rec@ block, whose continuation is its 'return'.
instance
  (Bind k (Term d g a) t One cont r', r ~ Ret tt r')
  => Bind k (Term d g (a :: SYN k)) t One (Ret tt cont) r
  where
  {-# INLINE (>>=) #-}
  x >>= k = Ret (x >>= \p -> unRet (k p))

-- | The body of a @rec@ block, tagged with the tuple of its variables. GHC's translation passes
-- that tuple to both 'return' and 'mfix', and this tag is what makes them the same.
type Ret :: Type -> Type -> Type
newtype Ret t x = Ret x

unRet :: Ret t x %1 -> x
unRet (Ret x) = x

-- | A pattern: a variable, @()@, or a pair of patterns. A triple or quadruple stands for pairs
-- nested to the left, as @a ':**' b ':**' c@ is: @(x, y, z)@ is @((x, y), z)@. Binding it at depth
-- @d@ to a term with context @g@ and type @a@, with a continuation with context @g'@ and type @c@.
-- A pair or @()@ at a computation, @'Up' a@, runs it and matches its value, so @c@ is then negative.
type Pat :: forall k -> Type -> Nat -> Ctx k -> SYN k -> Ctx k -> SYN k -> Constraint
class Pat k t d g a g' c where
  pat :: Term d g a %1 -> (t %1 -> Term (d + PSize t) g' c) %1 -> Term d (PCtx t d g a g') c

-- | The number of variables a pattern binds on the way, and so the depth it adds.
type PSize :: Type -> Nat
type family PSize t where
  PSize (x, y) = 2 + PSize x + PSize y
  PSize (x, y, z) = PSize ((x, y), z)
  PSize (w, x, y, z) = PSize (((w, x), y), z)
  PSize t = 0

-- | The context of a pattern match, from the context of the right hand side and of the
-- continuation.
type PCtx :: forall {k}. Type -> Nat -> Ctx k -> SYN k -> Ctx k -> Ctx k
type family PCtx t d g a g' where
  PCtx (x, y) d g (Not (Not a)) g' = Union g (Tail (PCtx (x, y) d '[ '(d, a)] a g'))
  PCtx (x, y) d g (a1 :** a2) g' = Union (Drop2 (PCtxPair x y d a1 a2 g')) g
  PCtx (x, y, z) d g a g' = PCtx ((x, y), z) d g a g'
  PCtx (w, x, y, z) d g a g' = PCtx (((w, x), y), z) d g a g'
  PCtx () d g a g' = Union g g'
  PCtx t d g a g' = g'

-- | The context of the body of the 'split' that a pair pattern starts with.
type PCtxPair :: forall {k}. Type -> Type -> Nat -> SYN k -> SYN k -> Ctx k -> Ctx k
type PCtxPair x y d a1 a2 g' =
  PCtx x (d + 2) '[ '(d, a1)] a1 (PCtx y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g')

-- The generic instances are incoherent: a variable pattern's type is often still unknown when the
-- instance is chosen, and a pair pattern's type is always a pair by then. The instances at a
-- computation are more specific, so they win once the type is known to be an 'Up'.

-- | The pattern @()@ at a computation of the unit runs it.
instance (Dialogue k, KnownObj y, c ~ Not y, Merge g g') => Pat k () d g (Not (Not I) :: SYN k) g' c where
  {-# INLINE pat #-}
  pat u k = case k () of
    MkTerm t -> runUp @d @g @g' @I @y u (withCtxOb @g' (t . rightUnitor @k @(Interp (Mul g'))))

-- | A pair pattern at a computation runs it and takes its value apart. The value needs no variable
-- of its own: the pattern's variables take the ids it would have taken.
instance
  ( Dialogue k
  , KnownObj a
  , KnownObj y
  , c ~ Not y
  , Pat k (x, y') d '[ '(d, a)] a g' c
  , PCtx (x, y') d '[ '(d, a)] a g' ~ ('(d, a) ': r)
  , Merge g r
  )
  => Pat k (x, y') d g (Not (Not a) :: SYN k) g' c
  where
  {-# INLINE pat #-}
  pat m k = case pat @k @(x, y') @d @'[ '(d, a)] @a @g' @c (var @d @a @d) k of
    MkTerm body -> runUp @d @g @r @a @y m (body . snoc @d @a @r)

-- | The pattern @()@ uses up a term of the unit type.
instance {-# INCOHERENT #-} (Monoidal k, a ~ I, KnownObj c, Merge g g') => Pat k () d g (a :: SYN k) g' c where
  {-# INLINE pat #-}
  pat (MkTerm u) k = case k () of
    MkTerm t -> withSynOb @c (MkTerm (leftUnitor @k @(Interp c) . (u M.** t) . merge @g @g'))

instance {-# INCOHERENT #-} (t ~ Term (DepthOf t) g a) => Pat k t d g a g' c where
  {-# INLINE pat #-}
  pat x k = k (recast x)

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
  {-# INLINE pat #-}
  pat s k =
    split
      s
      ( \a b ->
          pat @k @x @(d + 2) @'[ '(d, a1)] @a1 @(PCtx y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g') @c
            a
            (\px -> pat @k @y @(d + 2 + PSize x) @'[ '(d + 1, a2)] @a2 @g' @c b (\py -> k (px, py)))
      )

instance {-# INCOHERENT #-} (Pat k ((x, y), z) d g a g' c) => Pat k (x, y, z) d g a g' c where
  {-# INLINE pat #-}
  pat s k = pat @k @((x, y), z) @d @g @a @g' @c s (\((px, py), pz) -> k (px, py, pz))

instance {-# INCOHERENT #-} (Pat k (((w, x), y), z) d g a g' c) => Pat k (w, x, y, z) d g a g' c where
  {-# INLINE pat #-}
  pat s k = pat @k @(((w, x), y), z) @d @g @a @g' @c s (\(((pw, px), py), pz) -> k (pw, px, py, pz))

-- | The variables of a @rec@ block, as GHC tuples them up.
type RecVars :: Type -> Type -> Constraint
class RecVars k t | t -> k where
  type Vars k t :: Ctx k
  recVars :: t
  consume :: t %1 -> r %1 -> r

instance (Monoidal k, KnownObj (a :: SYN k)) => RecVars k (Term d '[ '(n, a)] a) where
  {-# INLINE recVars #-}
  {-# INLINE consume #-}
  type Vars k (Term d '[ '(n, a)] a) = '[ '(n, a)]
  recVars = var @n @a
  consume (MkTerm _) r = r

instance (RecVars k x, RecVars k y) => RecVars k (x, y) where
  {-# INLINE recVars #-}
  {-# INLINE consume #-}
  type Vars k (x, y) = Union (Vars k x) (Vars k y)
  recVars = (recVars, recVars)
  consume (x, y) r = consume x (consume y r)

instance (RecVars k x, RecVars k y, RecVars k z) => RecVars k (x, y, z) where
  {-# INLINE recVars #-}
  {-# INLINE consume #-}
  type Vars k (x, y, z) = Union (Vars k x) (Vars k (y, z))
  recVars = (recVars, recVars, recVars)
  consume (x, y, z) r = consume x (consume (y, z) r)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w) => RecVars k (x, y, z, w) where
  {-# INLINE recVars #-}
  {-# INLINE consume #-}
  type Vars k (x, y, z, w) = Union (Vars k x) (Vars k (y, z, w))
  recVars = (recVars, recVars, recVars, recVars)
  consume (x, y, z, w) r = consume x (consume (y, z, w) r)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v) => RecVars k (x, y, z, w, v) where
  {-# INLINE recVars #-}
  {-# INLINE consume #-}
  type Vars k (x, y, z, w, v) = Union (Vars k x) (Vars k (y, z, w, v))
  recVars = (recVars, recVars, recVars, recVars, recVars)
  consume (x, y, z, w, v) r = consume x (consume (y, z, w, v) r)

instance
  (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v, RecVars k u)
  => RecVars k (x, y, z, w, v, u)
  where
  {-# INLINE recVars #-}
  {-# INLINE consume #-}
  type Vars k (x, y, z, w, v, u) = Union (Vars k x) (Vars k (y, z, w, v, u))
  recVars = (recVars, recVars, recVars, recVars, recVars, recVars)
  consume (x, y, z, w, v, u) r = consume x (consume (y, z, w, v, u) r)

-- | The end of a @rec@ block: all its variables, as the tensor of their context.
{-# INLINE return #-}
return
  :: forall k t d. (Monoidal k, RecVars k t, KnownCtx (Vars k t)) => t %1 -> Ret t (Term d (Vars k t) (Mul (Vars k t)))
return t = Ret (consume t (MkTerm (ctxOb @(Vars k t))))

-- | A @rec@ block after tracing, from its context without the fed back variables to the variables
-- it passes on.
type Rec :: forall {k}. Nat -> Type -> Ctx k -> Ctx k -> Type
data Rec d t g0 outs where
  Rec :: (Interp (Mul g0) ~> Interp (Mul outs)) -> Rec d t g0 outs

-- | Trace a @rec@ block: the variables it uses before binding them are fed back.
{-# INLINE mfix #-}
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
  {-# INLINE (>>=) #-}
  Rec h >>= k = case k recVars of
    MkTerm body ->
      MkTerm
        ( body
            . unmerge @(Minus (CtxOf @k cont) outs) @outs
            . (ctxOb @(Minus (CtxOf @k cont) outs) M.** h)
            . merge @(Minus (CtxOf @k cont) outs) @g0
        )

-- | GHC's translation of @rec@ refers to @fail@, but pairs of variables always match.
fail :: a
fail = P.error "Proarrow.Tools.SMC.fail: a pattern did not match"

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
type Drop2 g = Tail (Tail g)

type Tail :: forall {k}. Ctx k -> Ctx k
type family Tail g where
  Tail (x ': g) = g

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
swapT = toSMC @(F a :** F b) \(a, b) -> b ** a

-- | Apply a function to an argument, both in a tensor.
--
-- >>> import Prelude (Bool (..), not)
-- >>> applyT @Bool @Bool (not, True)
-- False
applyT :: forall {k} (a :: k) b. (Closed k, SymMonoidal k, Ob a, Ob b) => (a ~~> b) ** a ~> b
applyT = toSMC @((F a :-> F b) :** F a) (\p -> split p (\f x -> f ! x))

-- | Curry the tensor.
--
-- >>> import Prelude (Bool (..))
-- >>> curryT @Bool @Bool True False
-- (True,False)
curryT :: forall {k} (a :: k) b. (Closed k, SymMonoidal k, Ob a, Ob b) => a ~> b ~~> a ** b
curryT = toSMC @(F a) @(F b :-> F a :** F b) (\x -> lam (\y -> x ** y))

-- | Rotate a triple, with a triple pattern.
--
-- >>> import Prelude (Bool (..), Int)
-- >>> rotT @Int @Bool @Int ((1, True), 2)
-- ((True,2),1)
rotT :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => a ** b ** c ~> b ** c ** a
rotT = toSMC @(F a :** F b :** F c) \(a, b, c) -> b ** c ** a

-- | Trace out @u@ with a @rec@ block. In 'Data.Kind.Type' the trace is a lazy fixed point.
--
-- >>> import Prelude (Int, take)
-- >>> traceT @Int @[Int] @[Int] (\(a, u) -> (take 3 u, a : u)) 1
-- [1,1,1]
traceT :: forall {k} (a :: k) b u. (TracedMonoidal k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
traceT h = toSMC @(F a) \a -> Proarrow.Tools.SMC.do
  rec (b, u) <- lift @(F a :** F u) @(F b :** F u) h (a ** u)
  b

-- | Trace out @u@ with 'loop'.
--
-- >>> import Prelude (Int, take)
-- >>> loopT @Int @[Int] @[Int] (\(a, u) -> (take 3 u, a : u)) 1
-- [1,1,1]
loopT :: forall {k} (a :: k) b u. (TracedMonoidal k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
loopT h = toSMC @(F a) \a -> loop @(F u) \u -> lift @(F a :** F u) @(F b :** F u) h (a ** u)

-- | A trace from the duality alone, so for any compact closed category: feed @u@ in along one
-- end of a new pair and join its new value with the other end.
loopCC :: forall {k} (a :: k) b u. (CompactClosed k, Ob a, Ob b, Ob u) => (a ** u ~> b ** u) -> a ~> b
loopCC h = toSMC @(F a) \a -> Proarrow.Tools.SMC.do
  (u, u') <- produce
  (b, v) <- lift @(F a :** F u) @(F b :** F u) h (a ** u)
  () <- annihilate u' v
  b

-- | A snake: create a pair, join its dual with the input, and continue with the other end. By the
-- zigzag law it is the identity. The input is older than the pair, so it sits to the left of it,
-- and the join needs a swap.
snakeT :: forall {k} (a :: k). (CompactClosed k, Ob a) => a ~> a
snakeT = toSMC @(F a) \x -> Proarrow.Tools.SMC.do
  (a, a') <- produce
  () <- annihilate a' x
  a

-- | The inverse of 'distribDual': make a pair for @a ** b@, and annihilate the two halves of its
-- plain end with the given duals.
combineDualT :: forall {k} (a :: k) b. (CompactClosed k, Ob a, Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDualT = toSMC @(Not (F a) :** Not (F b)) @(Not (F a :** F b)) \(da, db) -> Proarrow.Tools.SMC.do
  (ab, ab') <- produce
  (a, b) <- ab
  () <- annihilate da a
  () <- annihilate db b
  ab'

-- | The tensor distributes over the coproduct: the shared @a@ goes to whichever branch is taken.
--
-- >>> import Prelude (Bool (..), Char, Either (..), Int)
-- >>> distT @Int @Bool @Char (1, Left True)
-- Left (1,True)
distT
  :: forall {k} (a :: k) b c. (Distributive k, SymMonoidal k, Ob a, Ob b, Ob c) => a ** (b || c) ~> (a ** b) || (a ** c)
distT = toSMC @(F a :** (F b :|| F c)) \(a, bc) ->
  caseOf a bc (\(a', b) -> inl (a' ** b)) (\(a', c) -> inr (a' ** c))

-- | Swap a coproduct, with nothing to share.
--
-- >>> import Prelude (Bool (..), Either (..), Int)
-- >>> swapEitherT @Int @Bool (Left 1)
-- Right 1
swapEitherT :: forall {k} (a :: k) b. (Distributive k, SymMonoidal k, Ob a, Ob b) => a || b ~> b || a
swapEitherT = toSMC @(F a :|| F b) \x ->
  caseOf unit x (\((), a) -> inr a) (\((), b) -> inl b)

-- | A pair both as it is and swapped: each alternative takes the same pair apart in its own way.
--
-- >>> import Prelude (Bool (..), Int)
-- >>> bothWaysT @Int @Bool (1, True)
-- ((1,True),(True,1))
bothWaysT
  :: forall {k} (a :: k) b. (SymMonoidal k, HasBinaryProducts k, Ob a, Ob b) => a ** b ~> (a ** b) && (b ** a)
bothWaysT = toSMC @(F a :** F b) \p -> with (\q -> q) (\(x, y) -> y ** x) p

-- | Double negation introduction: a consumer of a consumer of @a@ hands it the @a@. This is
-- 'ret', written out.
dniT :: forall {k} (a :: k). (Dialogue k, Ob a) => a ~> Dual (Dual a)
dniT = toSMC @(F a) @(Up (F a)) \x -> cont (x |>)

-- | Double negation elimination, the classical direction: a computation is its value. Binding its
-- consumer with 'cont' and cutting would only give the computation back.
dneT :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
dneT = toSMC @(Up (F a)) @(F a) \nn -> classical nn

-- | Sequencing: run the input computation, and continue with @f@ on its value. In a category with
-- @'Dual' a = a ~~> r@ this is the bind of the continuation monad.
bindT :: forall {k} (a :: k) b. (Dialogue k, Ob a, Ob b) => (a ~> Dual (Dual b)) -> Dual (Dual a) ~> Dual (Dual b)
bindT f = toSMC @(Up (F a)) @(Up (F b)) \m -> Proarrow.Tools.SMC.do
  x <- m
  lift @(F a) @(Up (F b)) f x

-- | Contraposition: a consumer of @b@ consumes @a@ through @f@.
contraT :: forall {k} (a :: k) b. (Dialogue k, Ob a, Ob b) => (a ~> b) -> Dual b ~> Dual a
contraT f = toSMC @(Not (F b)) @(Not (F a)) \nb -> cont \x -> cut nb (lift @(F a) @(F b) f x)

-- | Par is symmetric: bind both outputs and hand them to the input the other way round. This is
-- 'Proarrow.Category.Monoidal.Dialogue.parSwap'.
parSwapT :: forall {k} (a :: k) b. (Dialogue k, Ob a, Ob b) => Par a b ~> Par b a
parSwapT = toSMC @(F a :## F b) @(F b :## F a) \p -> cont \(kb, ka) -> ka ** kb |> p

-- | Linear (weak) distributivity, @a ⊗ (b ⅋ c) ⊸ (a ⊗ b) ⅋ c@: the @b@ the input emits is paired
-- with @a@ and sent to the first output, and its @c@ goes to the second. This is
-- 'Proarrow.Category.Monoidal.Dialogue.weakDistL'.
weakDistT
  :: forall {k} (a :: k) b c
   . (Dialogue k, Ob a, Ob b, Ob c)
  => a ** Par b c ~> Par (a ** b) c
weakDistT = toSMC @(F a :** (F b :## F c)) @((F a :** F b) :## F c) \(a, bc) ->
  cont \(kab, kc) -> cont (\b -> a ** b |> kab) ** kc |> bc

-- | The snake on the dual: join the input with the first end of a new pair, and continue with the
-- second. Here the wires meet in the order they come, so no swap is needed.
snakeDualT :: forall {k} (a :: k). (CompactClosed k, Ob a) => Dual a ~> Dual a
snakeDualT = toSMC @(Not (F a)) \x -> Proarrow.Tools.SMC.do
  (a, a') <- produce
  () <- annihilate x a
  a'
