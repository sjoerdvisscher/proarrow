{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | A HOAS front end for building morphisms in any symmetric monoidal category, the
-- resource-aware counterpart of "Proarrow.Tools.CCC", which grows with the structure of the target: traces,
-- duals, additives, and the polarised System L reading of inputs and outputs in a dialogue
-- category. A 'Term' is indexed by its context, the variables it uses, so a variable is the
-- identity on its own type. Terms combine by merging their contexts, which reorders wires. A
-- variable used exactly once needs nothing more. One that two terms both use is copied, which needs
-- a 'CocommutativeComonoid' on its type, and one that its binder's body does not use is discarded,
-- which needs a 'Comonoid'. So the types ask for copying and discarding only where a term does it.
--
-- Copying a variable copies the value it stands for. A Haskell function that uses its argument
-- twice uses the term it is given twice, so in a category where copying is not natural, a term to
-- be shared should be bound to a variable first, with a bind in @do@ notation.
--
-- A variable's type records the binding depth at which it is used, so a variable used both outside
-- and inside a binder needs 'recast' at the inner use: @x ** lam (\\z -> recast x ** z)@.
--
-- Types are 'SYN' expressions, interpreted in the target category by 'Interp'. Their tensor is a
-- constructor, so a pattern can take a term's type apart, which the target's own @**@, a type
-- family, would not allow.
--
-- Every variable has an id, the number of binders around it, and a context lists its variables
-- by descending id. Merging compares ids, so it only reduces where the depths are known, which is
-- the case for terms built directly inside 'toSMC'. A reusable piece is compiled on its own with
-- 'toSMC' and used with 'lift', with no inputs from @'I'@. 'toSMC' starts again at depth 0, so it
-- must not be used inside another term: a variable of that term used in it could be taken for one
-- of its own. Inside a term, bind with @do@ notation instead.
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
-- the variables that the block itself uses, @bm@ and @bp@ above, are fed back, and the ones the
-- rest of the @do@ block uses are passed on to it. A variable that both use is copied, and one that
-- neither uses is discarded. GHC's translation of @rec@ passes every variable of the block to its end again,
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
  , KnownObj

    -- * Patterns
    -- $patterns

    -- * Terms

    -- ** Symmetric monoidal categories
  , Term
  , toSMC
  , lift
  , unit
  , (**)
  , split
  , Tuple
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

    -- ** Hypergraph categories: index notation
    -- $index
  , sumOver
  , delta
  , (*^)
  , (^*)

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
  , KnownCtx
  , Union
  , Merge
  , Thin
  , BindVar

    -- * Do notation
  , (>>=)
  , return
  , mfix
  , fail
  , Bind
  , Binds

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
  , matMulT
  , traceIdxT
  , hadamardT
  , swapEitherT
  ) where

import Data.Kind (Constraint, Type)
import GHC.TypeNats (CmpNat, Nat, type (+))
import Prelude (Ordering (..), type (~))
import Prelude qualified as P

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , SymMonoidal (..)
  , Tensor
  , associator'
  , associatorInv'
  , rightUnitorInvWith
  , rightUnitorWith
  , swapInner
  )
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..), Par, bindDual, dualityCounitSA)
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, cap)
import Proarrow.Category.Monoidal.IsoMix (IsoMix (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal, trace)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..), Monoid (..))
import Proarrow.Object (Obj)

infixl 7 **
infixl 1 |>
infixl 8 !
infixl 7 *^
infixl 7 ^*
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
  UnionBy EQ (x ': g1) (y ': g2) = x ': Union g1 g2

-- | The newest variable split off the tensor of a context, the inverse of 'snoc'.
{-# INLINE unsnoc #-}
unsnoc
  :: forall {k} n (a :: SYN k) g
   . (Monoidal k, KnownObj a, KnownCtx g) => Interp (Mul ('(n, a) ': g)) ~> Interp (Mul g) ** Interp a
unsnoc = ctxCase @g (withSynOb @a leftUnitorInv) (ctxOb @('(n, a) ': g))

-- | Split the tensor of the union of two contexts into the tensors of the two contexts. This is
-- where the wires are reordered, the only place 'swap' is used, and where a variable that both
-- contexts have is copied.
type Merge :: forall {k}. Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => Merge (g1 :: Ctx k) g2 where
  merge :: Interp (Mul (Union g1 g2)) ~> Interp (Mul g1) ** Interp (Mul g2)

instance (Monoidal k, KnownCtx g2) => Merge ('[] :: Ctx k) g2 where
  {-# INLINE merge #-}
  merge = withCtxOb @g2 leftUnitorInv

instance (Monoidal k, KnownCtx ('(n, a) ': g1)) => Merge ('(n, a) ': g1 :: Ctx k) '[] where
  {-# INLINE merge #-}
  merge = withCtxOb @('(n, a) ': g1) rightUnitorInv

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
  merge = mergeBy @(CmpNat n m) @('(n, a) ': g1) @('(m, b) ': g2)

-- | 'merge' for two non-empty contexts, by which of the two has the larger head id.
type MergeBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => MergeBy o (g1 :: Ctx k) g2 where
  mergeBy :: Interp (Mul (UnionBy o g1 g2)) ~> Interp (Mul g1) ** Interp (Mul g2)

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
  mergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( associator' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
          . (merge @('(n, a) ': g1) @g2 M.** synOb @b)
      )

-- | A variable both contexts have is copied, one copy for each side.
instance
  ( SymMonoidal k
  , CocommutativeComonoid (Interp a)
  , KnownObj (a :: SYN k)
  , a ~ b
  , Merge g1 g2
  , KnownCtx (Union g1 g2)
  )
  => MergeBy EQ ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE mergeBy #-}
  mergeBy = ctxCase @g1 (ctxCase @g2 (comult @(Interp a)) withRest) withRest
    where
      -- When the variable is all both sides have, this is just the copy.
      withRest :: Interp (Mul ('(n, a) ': Union g1 g2)) ~> Interp (Mul ('(n, a) ': g1)) ** Interp (Mul ('(m, b) ': g2))
      withRest =
        withCtxOb @g1
          ( withCtxOb @g2
              ( withSynOb @a
                  ( (snoc @n @a @g1 M.** snoc @m @a @g2)
                      . swapInner @(Interp (Mul g1)) @(Interp (Mul g2)) @(Interp a) @(Interp a)
                      . (merge @g1 @g2 M.** comult @(Interp a))
                      . unsnoc @n @a @(Union g1 g2)
                  )
              )
          )

-- | The inverse of 'merge' for two contexts without a variable in common, which a @rec@ block
-- uses to put the wires it feeds back together with the others.
type Unmerge :: forall {k}. Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => Unmerge (g1 :: Ctx k) g2 where
  unmerge :: Interp (Mul g1) ** Interp (Mul g2) ~> Interp (Mul (Union g1 g2))

instance (Monoidal k, KnownCtx g2) => Unmerge ('[] :: Ctx k) g2 where
  {-# INLINE unmerge #-}
  unmerge = withCtxOb @g2 leftUnitor

instance (Monoidal k, KnownCtx ('(n, a) ': g1)) => Unmerge ('(n, a) ': g1 :: Ctx k) '[] where
  {-# INLINE unmerge #-}
  unmerge = withCtxOb @('(n, a) ': g1) rightUnitor

instance
  ( Monoidal k
  , KnownObj a
  , KnownObj b
  , KnownCtx g1
  , KnownCtx g2
  , UnmergeBy (CmpNat n m) ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  )
  => Unmerge ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  where
  {-# INLINE unmerge #-}
  unmerge = unmergeBy @(CmpNat n m) @('(n, a) ': g1) @('(m, b) ': g2)

-- | 'unmerge' for two non-empty contexts, by which of the two has the larger head id.
type UnmergeBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => UnmergeBy o (g1 :: Ctx k) g2 where
  unmergeBy :: Interp (Mul g1) ** Interp (Mul g2) ~> Interp (Mul (UnionBy o g1 g2))

instance
  ( SymMonoidal k
  , Unmerge g1 ('(m, b) ': g2)
  , KnownObj (a :: SYN k)
  , KnownObj b
  , Mul ('(n, a) ': Union g1 ('(m, b) ': g2)) ~ (Mul (Union g1 ('(m, b) ': g2)) :** a)
  )
  => UnmergeBy GT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE unmergeBy #-}
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
  , Unmerge ('(n, a) ': g1) g2
  , KnownObj a
  , KnownObj (b :: SYN k)
  , Mul ('(m, b) ': Union ('(n, a) ': g1) g2) ~ (Mul (Union ('(n, a) ': g1) g2) :** b)
  )
  => UnmergeBy LT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE unmergeBy #-}
  unmergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( (unmerge @('(n, a) ': g1) @g2 M.** synOb @b)
          . associatorInv' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
      )

-- | Keep the variables of @g@ that @h@ has and discard the others, for an alternative of the
-- additives that does not use all the variables of the other. Every variable of @h@ must be in
-- @g@.
type Thin :: forall {k}. Ctx k -> Ctx k -> Constraint
class (KnownCtx g, KnownCtx h) => Thin (g :: Ctx k) h where
  thin :: Interp (Mul g) ~> Interp (Mul h)

instance (Monoidal k) => Thin ('[] :: Ctx k) '[] where
  {-# INLINE thin #-}
  thin = obj @(Unit :: k)

instance (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k), Thin g '[]) => Thin ('(n, a) ': g) '[] where
  {-# INLINE thin #-}
  thin = leftUnitor @k @Unit . (thin @g @'[] M.** counit @(Interp a)) . unsnoc @n @a @g

instance
  (KnownObj a, KnownObj b, KnownCtx g, KnownCtx h, ThinBy (CmpNat n m) ('(n, a) ': g) ('(m, b) ': h))
  => Thin ('(n, a) ': g :: Ctx k) ('(m, b) ': h)
  where
  {-# INLINE thin #-}
  thin = thinBy @(CmpNat n m) @('(n, a) ': g) @('(m, b) ': h)

-- | 'thin' for two non-empty contexts, by which of the two has the larger head id.
type ThinBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Constraint
class (KnownCtx g, KnownCtx h) => ThinBy o (g :: Ctx k) h where
  thinBy :: Interp (Mul g) ~> Interp (Mul h)

instance (Monoidal k, KnownObj (a :: SYN k), a ~ b, Thin g h) => ThinBy EQ ('(n, a) ': g) ('(m, b) ': h) where
  {-# INLINE thinBy #-}
  thinBy = withSynOb @a (snoc @m @a @h . (thin @g @h M.** synOb @a) . unsnoc @n @a @g)

instance
  (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k), KnownObj b, Thin g ('(m, b) ': h))
  => ThinBy GT ('(n, a) ': g) ('(m, b) ': h)
  where
  {-# INLINE thinBy #-}
  thinBy =
    withCtxOb @('(m, b) ': h)
      (rightUnitor . (thin @g @('(m, b) ': h) M.** counit @(Interp a)) . unsnoc @n @a @g)

-- | A binder's variable @n@ on the right of @r@, what the body uses besides it, given the body's
-- context @g@: 'snoc' if the body uses the variable, and its counit otherwise. The binder's
-- variable is the newest in scope, so it can only be at the head of @g@. The functional
-- dependency, rather than a type family, gives @r@, so that a binder costs one comparison of ids.
type BindVar :: forall {k}. Nat -> SYN k -> Ctx k -> Ctx k -> Constraint
class (KnownCtx r) => BindVar n (a :: SYN k) g r | n g -> r where
  bindVar :: Interp (Mul r) ** Interp a ~> Interp (Mul g)

instance (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k)) => BindVar n a '[] '[] where
  {-# INLINE bindVar #-}
  bindVar = rightUnitorWith @Unit (counit @(Interp a))

instance (KnownCtx r, BindVarBy (CmpNat n m) n a ('(m, b) ': g) r) => BindVar n (a :: SYN k) ('(m, b) ': g) r where
  {-# INLINE bindVar #-}
  bindVar = bindVarBy @(CmpNat n m) @n @a @('(m, b) ': g) @r

-- | 'bindVar' for a non-empty context, by whether its head is the new variable.
type BindVarBy :: forall {k}. Ordering -> Nat -> SYN k -> Ctx k -> Ctx k -> Constraint
class BindVarBy o n (a :: SYN k) g r | o n g -> r where
  bindVarBy :: Interp (Mul r) ** Interp a ~> Interp (Mul g)

instance (Monoidal k, KnownObj (a :: SYN k), a ~ b, KnownCtx g) => BindVarBy EQ n a ('(m, b) ': g) g where
  {-# INLINE bindVarBy #-}
  bindVarBy = snoc @m @a @g

instance
  (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k), KnownObj b, KnownCtx g)
  => BindVarBy GT n a ('(m, b) ': g) ('(m, b) ': g)
  where
  {-# INLINE bindVarBy #-}
  bindVarBy =
    withCtxOb @('(m, b) ': g)
      (rightUnitorWith @(Interp (Mul ('(m, b) ': g))) (counit @(Interp a)))

-- | The variable with id @n@: the identity on its type.
{-# INLINE var #-}
var :: forall {k} n (a :: SYN k) d. (CategoryOf k, KnownObj a) => Term d '[ '(n, a)] a
var = withSynOb @a (MkTerm (obj @(Interp a)))

-- $patterns
-- Wherever a function on terms receives an input, that is the function given to 'toSMC', 'lam',
-- 'loop' and 'cont', the alternatives of 'with' and 'caseOf', and the left of a bind in @do@
-- notation, the input arrives through a pattern: a variable, @()@, or a tuple of patterns. A
-- variable stands for the whole input, whatever its type, and is discarded if it is not used. @()@
-- matches the unit 'I'. A pair matches a tensor @a ':**' b@ and binds its two sides, and a triple
-- or quadruple is pairs nested to the left, as @a ':**' b ':**' c@ is. At a computation,
-- @'Up' (a ':**' b)@ or @'Up' 'I'@, a pair or @()@ pattern runs the computation and matches its
-- value, so the rest of the block must be of a negative type; a variable at a computation only
-- names it.
--
-- Tuples build terms as well, the mirror image of taking them apart: 'ret' of a tuple makes a pair
-- at a tensor into '(**)' of its parts and a pair at a computation into the computation of the
-- pair.

-- | Compile a function on terms to a morphism. The function receives the input through a pattern
-- (see /Patterns/), so @()@ compiles a term without inputs and a tuple takes a tensor apart.
{-# INLINE toSMC #-}
toSMC
  :: forall {k} (a :: SYN k) b t cont
   . (Monoidal k, Binds 0 '[] a b t cont)
  => (t -> cont)
  -> Interp a ~> Interp b
toSMC k = withSynOb @a (bound @0 @'[] @a @b k . leftUnitorInv @k @(Interp a))

-- | Copy a term whose type is a comonoid: @(x1, x2) <- dup x@. Using a variable twice copies it too,
-- but needs a 'CocommutativeComonoid'; 'dup' needs only a 'Comonoid', and its two copies come out
-- in the order of 'comult'.
{-# INLINE dup #-}
dup :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s -> Term d g (s :** s)
dup = lift @s @(s :** s) comult

-- | Discard a term whose type is a comonoid: @() <- drop t@. A variable that is not used is
-- discarded without it.
{-# INLINE drop #-}
drop :: forall {k} (s :: SYN k) d g. (Comonoid (Interp s)) => Term d g s -> Term d g I
drop = lift @s @I counit

-- | Lift a morphism of the target category to a function on terms.
{-# INLINE lift #-}
lift :: forall {k} (a :: SYN k) b d g. (CategoryOf k) => (Interp a ~> Interp b) -> Term d g a -> Term d g b
lift f (MkTerm t) = MkTerm (f . t)

-- | Two terms side by side. A variable both use is copied.
{-# INLINE (**) #-}
(**)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Monoidal k, Merge g1 g2)
  => Term d g1 a -> Term d g2 b -> Term d (Union g1 g2) (a :** b)
MkTerm f ** MkTerm g = MkTerm ((f M.** g) . merge @g1 @g2)

-- | Two new variables @n@ and @n + 1@, of types @a@ and @b@, for the body of a 'split' whose
-- context is @g'@: the tensor @a ':**' b@, given from the context @g@, next to @r@, what the body
-- uses besides them.
{-# INLINE push2 #-}
push2
  :: forall {k} n (a :: SYN k) b g' r1 r g
   . (Monoidal k, KnownObj a, KnownObj b, BindVar (n + 1) b g' r1, BindVar n a r1 r, Merge r g)
  => (Interp (Mul g) ~> Interp a ** Interp b)
  -> Interp (Mul (Union r g)) ~> Interp (Mul g')
push2 p =
  withCtxOb @r
    ( withSynOb @b
        ( bindVar @(n + 1) @b @g' @r1
            . (bindVar @n @a @r1 @r M.** obj @(Interp b))
            . associatorInv' (ctxOb @r) (synOb @a) (synOb @b)
            . (ctxOb @r M.** p)
            . merge @r @g
        )
    )

-- | Take a tensor apart: the continuation gets a variable for each side.
{-# INLINE split #-}
split
  :: forall {k} d g g' r1 r (a :: SYN k) b c da db
   . (Monoidal k, KnownObj a, KnownObj b, BindVar (d + 1) b g' r1, BindVar d a r1 r, Merge r g)
  => Term d g (a :** b)
  -> (Term da '[ '(d, a)] a -> Term db '[ '(d + 1, b)] b -> Term (d + 2) g' c)
  -> Term d (Union r g) c
split (MkTerm p) k = case k (var @d @a) (var @(d + 1) @b) of
  MkTerm body -> MkTerm (body . push2 @d @a @b @g' @r1 @r @g p)

-- | The unit, which uses no variables.
{-# INLINE unit #-}
unit :: forall {k} d. (Monoidal k) => Term d ('[] :: Ctx k) I
unit = MkTerm id

-- | A function: the body receives the argument through a pattern (see /Patterns/). This needs the
-- category to be closed.
{-# INLINE lam #-}
lam
  :: forall {k} d r (a :: SYN k) b t cont
   . (Closed k, Binds d r a b t cont)
  => (t -> cont)
  -> Term d r (a :-> b)
lam k = withCtxOb @r (withSynOb @a (MkTerm (curry @k @(Interp (Mul r)) @(Interp a) (bound @d @r @a @b k))))

-- | Trace: the body receives the value fed back through a pattern (see /Patterns/), and returns
-- it again next to the result. This needs the category to be traced.
{-# INLINE loop #-}
loop
  :: forall {k} (u :: SYN k) b d r t cont
   . (TracedMonoidal k, KnownObj b, Binds d r u (b :** u) t cont)
  => (t -> cont)
  -> Term d r b
loop k =
  withCtxOb @r
    ( withSynOb @u
        (withSynOb @b (MkTerm (trace @(~>) @(Interp u) @(Interp (Mul r)) @(Interp b) (bound @d @r @u @(b :** u) k))))
    )

-- $index
-- Index notation, as in Einstein summation, for a category whose index types are special
-- commutative Frobenius algebras, such as a hypergraph category. An index is a variable whose type
-- is such an object. Using an index more than once copies it, so every use sees the same value,
-- and 'sumOver' binds an index that is summed over. 'delta' says that two wires carry the same
-- value, which is how a morphism lifted onto an index is tied to another index: in "Proarrow.Category.Instance.Mat",
-- @'delta' ('lift' f i) j@ is the entry of @f@ at @i@ and @j@. A term of type 'I' is a scalar, and
-- @(*^)@ and @(^*)@ multiply a term by one. An output index is a summed index that the term also
-- returns, so matrix multiplication is 'matMulT':
--
-- > \i -> sumOver \k -> sumOver \j -> delta (lift f i) j *^ delta (lift g j) k *^ k
--
-- What the sum is depends on the category: in 'Proarrow.Category.Instance.Mat.Mat' it is the sum
-- of numbers, in 'Proarrow.Category.Instance.FinRel.FinRel' it is "there is", and in the diagram
-- categories it is a wire with no end on the boundary.

-- | An index summed over: the binder's variable is fed by the unit of its type's monoid, which,
-- copied to every use, is the sum over all the values the index can take. The body receives the
-- index through a pattern (see /Patterns/).
{-# INLINE sumOver #-}
sumOver
  :: forall {k} (a :: SYN k) d r b t cont
   . (Monoidal k, Frobenius (Interp a), Binds d r a b t cont)
  => (t -> cont)
  -> Term d r b
sumOver k =
  withCtxOb @r
    ( withSynOb @a
        ( MkTerm
            (bound @d @r @a @b k . rightUnitorInvWith @(Interp (Mul r)) (mempty @(Interp a)))
        )
    )

-- | The Kronecker delta: the scalar that says two wires of an index type carry the same value. It
-- is the cap of the Frobenius algebra, @'counit' . 'mappend'@.
{-# INLINE delta #-}
delta
  :: forall {k} (a :: SYN k) d g1 g2
   . (Frobenius (Interp a), KnownObj a, Merge g1 g2)
  => Term d g1 a -> Term d g2 a -> Term d (Union g1 g2) I
delta x y = lift @(a :** a) @I (cap @(Interp a)) (x ** y)

-- | A term multiplied by a scalar on its left. At 'I' it is the product of two scalars.
{-# INLINE (*^) #-}
(*^)
  :: forall {k} d g1 g2 (a :: SYN k)
   . (Monoidal k, KnownObj a, Merge g1 g2)
  => Term d g1 I -> Term d g2 a -> Term d (Union g1 g2) a
s *^ x = lift @(I :** a) @a (withSynOb @a (leftUnitor @k @(Interp a))) (s ** x)

-- | A term multiplied by a scalar on its right.
{-# INLINE (^*) #-}
(^*)
  :: forall {k} d g1 g2 (a :: SYN k)
   . (Monoidal k, KnownObj a, Merge g1 g2)
  => Term d g1 a -> Term d g2 I -> Term d (Union g1 g2) a
x ^* s = lift @(a :** I) @a (withSynOb @a (rightUnitor @k @(Interp a))) (x ** s)

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
  => Consumer d g1 a -> Term d g2 a -> Term d (Union g1 g2) I
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
  => Consumer d g1 a -> Term d g2 a -> Command d (Union g1 g2)
cut x y = lift @(Not a :** a) @(Not I) (withSynOb @a (dualityCounitSA @(Interp a))) (x ** y)

-- | 'cut' with the producer first, as System L writes @⟨t | k⟩@: @t |> k@ sends @t@ into @k@.
{-# INLINE (|>) #-}
(|>)
  :: forall {k} (a :: SYN k) d g1 g2
   . (Dialogue k, KnownObj a, Merge g2 g1)
  => Term d g1 a -> Consumer d g2 a -> Command d (Union g2 g1)
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
   . (Dialogue k, Binds d r a (Not I) t cont)
  => (t -> cont)
  -> Term d r (Not a)
cont k =
  withCtxOb @r
    ( withSynOb @a
        ( MkTerm
            ( dual (rightUnitorInv @k @(Interp a))
                . linDist @k @(Interp (Mul r)) @(Interp a) @Unit (bound @d @r @a @(Not I) k)
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
  -> (Interp (Mul r) ** Interp a ~> Interp (Not y))
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
  => t -> Term (TupleDepth t) (TupleCtx k t) (Up a)
ret t = withSynOb @a (lift @a @(Up a) (doubleNegInv @k @(Interp a))) (tuple @k @t @a t)

-- | A term built from a tuple of terms, by the type it is expected to have: a term is itself, a
-- pair at a tensor is the tensor of its parts, and a pair at a computation @'Up' a@ is the
-- computation of the pair at @a@. A triple or quadruple stands for pairs nested to the left, as in
-- patterns. The parts must be at the same depth, and their contexts are merged.
type Tuple :: forall k -> Type -> SYN k -> Constraint
class Tuple k t a where
  tuple :: t -> Term (TupleDepth t) (TupleCtx k t) a

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
recast :: forall {k} (a :: SYN k) b d d' g. (Interp a ~ Interp b) => Term d g a -> Term d' g b
recast (MkTerm f) = MkTerm f

-- | Store a term of a negative type as a value: the same morphism at the positive type @'Dn' n@,
-- which a bind names instead of running. This is call by push value's @thunk@, 'recast' to 'Dn'.
{-# INLINE thunk #-}
thunk :: forall {k} (n :: SYN k) d g. Term d g n -> Term d g (Dn n)
thunk = recast

-- | A stored term at its negative type again, where a bind runs it. This is call by push value's
-- @force@, 'recast' from 'Dn'.
{-# INLINE force #-}
force :: forall {k} (n :: SYN k) d g. Term d g (Dn n) -> Term d g n
force = recast

-- | A computation as its value again: double negation elimination, which only a *-autonomous
-- category has. There every type is equivalent to its shift, so the polarities collapse.
{-# INLINE classical #-}
classical :: forall {k} (a :: SYN k) d g. (StarAutonomous k, KnownObj a) => Term d g (Up a) -> Term d g a
classical = withSynOb @a (lift @(Up a) @a (doubleNeg @k @(Interp a)))

-- $additives
-- The additives share their context between alternatives, of which only one is used, so a
-- variable that several alternatives use is not copied. One that an alternative does not use is
-- discarded there.

-- | Both of two alternatives over the same variables: the product. This needs products.
{-# INLINE with #-}
with
  :: forall {k} (a :: SYN k) b d g1 g2
   . (HasBinaryProducts k, Thin (Union g1 g2) g1, Thin (Union g1 g2) g2)
  => Term d g1 a
  -> Term d g2 b
  -> Term d (Union g1 g2) (a :&& b)
with (MkTerm f) (MkTerm h) = MkTerm ((f . thin @(Union g1 g2) @g1) &&& (h . thin @(Union g1 g2) @g2))

-- | The first alternative of a product.
{-# INLINE exl #-}
exl
  :: forall {k} (a :: SYN k) b d g. (HasBinaryProducts k, KnownObj a, KnownObj b) => Term d g (a :&& b) -> Term d g a
exl = lift @(a :&& b) @a (withSynOb @a (withSynOb @b (fst @k @(Interp a) @(Interp b))))

-- | The second alternative of a product.
{-# INLINE exr #-}
exr
  :: forall {k} (a :: SYN k) b d g. (HasBinaryProducts k, KnownObj a, KnownObj b) => Term d g (a :&& b) -> Term d g b
exr = lift @(a :&& b) @b (withSynOb @a (withSynOb @b (snd @k @(Interp a) @(Interp b))))

-- | Use up a term into the unit of the product.
{-# INLINE absorb #-}
absorb :: forall {k} (s :: SYN k) d g. (HasTerminalObject k, KnownObj s) => Term d g s -> Term d g Top
absorb = lift @s @Top (withSynOb @s (terminate @k @(Interp s)))

-- | The left injection into a coproduct.
{-# INLINE inl #-}
inl
  :: forall {k} (a :: SYN k) b d g
   . (HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => Term d g a -> Term d g (a :|| b)
inl = lift @a @(a :|| b) (withSynOb @a (withSynOb @b (lft @k @(Interp a) @(Interp b))))

-- | The right injection into a coproduct.
{-# INLINE inr #-}
inr
  :: forall {k} (a :: SYN k) b d g
   . (HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => Term d g b -> Term d g (a :|| b)
inr = lift @b @(a :|| b) (withSynOb @a (withSynOb @b (rgt @k @(Interp a) @(Interp b))))

-- | Case analysis on a coproduct. Each branch receives the contents of its alternative through a
-- pattern (see /Patterns/), and the variables of the term around it are shared between the
-- branches. This needs the tensor to distribute over the coproduct.
{-# INLINE caseOf #-}
caseOf
  :: forall {k} (a :: SYN k) b c d g r1 r2 t1 cont1 t2 cont2
   . ( Distributive k
     , KnownObj a
     , KnownObj b
     , Binds d r1 a c t1 cont1
     , Binds d r2 b c t2 cont2
     , Thin (Union r1 r2) r1
     , Thin (Union r1 r2) r2
     , Merge (Union r1 r2) g
     )
  => Term d g (a :|| b)
  -> (t1 -> cont1)
  -> (t2 -> cont2)
  -> Term d (Union (Union r1 r2) g) c
caseOf (MkTerm x) f h =
  withCtxOb @(Union r1 r2)
    ( withSynOb @a
        ( withSynOb @b
            ( MkTerm
                ( ( (bound @d @r1 @a @c f . (thin @(Union r1 r2) @r1 M.** obj @(Interp a)))
                      ||| (bound @d @r2 @b @c h . (thin @(Union r1 r2) @r2 M.** obj @(Interp b)))
                  )
                    . distL @k @(Interp (Mul (Union r1 r2))) @(Interp a) @(Interp b)
                    . (ctxOb @(Union r1 r2) M.** x)
                    . merge @(Union r1 r2) @g
                )
            )
        )
    )

-- | There is no term of 'Zero', so from one, together with the rest of the context, anything
-- follows.
{-# INLINE absurd #-}
absurd
  :: forall {k} (s :: SYN k) c d g1 g2
   . (Distributive k, KnownObj s, KnownObj c, Merge g1 g2)
  => Term d g1 s -> Term d g2 Zero -> Term d (Union g1 g2) c
absurd e z = lift @(s :** Zero) @c (withSynOb @s (withSynOb @c (initiate @k @(Interp c) . absorbL @k @(Interp s)))) (e ** z)

-- | Function application. A variable both the function and its argument use is copied.
{-# INLINE (!) #-}
(!)
  :: forall {k} d g1 g2 (a :: SYN k) b
   . (Closed k, KnownObj a, KnownObj b, Merge g1 g2)
  => Term d g1 (a :-> b) -> Term d g2 a -> Term d (Union g1 g2) b
MkTerm f ! MkTerm x =
  withSynOb @a (withSynOb @b (MkTerm (apply @k @(Interp a) @(Interp b) . (f M.** x) . merge @g1 @g2)))

-- Do notation

-- | The pattern @t@ of a binder: it takes apart the variable @(n, a)@, and the binder's body
-- @cont@ then gives a term at depth @n + 1@ with type @b@, whose context is @g@ and possibly that
-- variable. Both the variable's type and the rest of the context must be known.
type Binds :: forall {k}. Nat -> Ctx k -> SYN k -> SYN k -> Type -> Type -> Constraint
class (KnownObj a, KnownCtx g) => Binds n g (a :: SYN k) b t cont where
  -- | The body of a binder, with the pattern taking apart its new variable, as a morphism from the
  -- context around it and the variable. This is what 'toSMC', 'lam', 'loop', 'cont', 'caseOf',
  -- 'sumOver' and the binds of @do@ notation share.
  bound :: (t -> cont) -> Interp (Mul g) ** Interp a ~> Interp b

-- The context of the body is @g'@, which only the instance needs to name.
instance
  ( KnownObj a
  , KnownCtx g
  , BindPat k (Term (n + 1) '[ '(n, a)] a) t cont (Term (n + 1) g' b)
  , BindVar n a g' g
  )
  => Binds n g (a :: SYN k) b t cont
  where
  {-# INLINE bound #-}
  bound k = case bindPat @k @(Term (n + 1) '[ '(n, a)] a) @t @cont @(Term (n + 1) g' b) (var @n @a @(n + 1)) k of
    MkTerm body -> body . bindVar @n @a @g' @g

-- | A bind in a @do@ block: a term taken apart by a pattern, or the variables of a @rec@ block.
type Bind :: Type -> Type -> Type -> Type -> Type -> Constraint
class Bind k m t cont r | m -> k where
  -- | Bind the right hand side to the pattern of the continuation.
  (>>=) :: m -> (t -> cont) -> r

-- | A term on the right hand side is taken apart by the pattern. Incoherent, so that it is chosen
-- as soon as the right hand side is known, unless the right hand side is a computation.
instance {-# INCOHERENT #-} (BindTerm k t (Term d g a) cont r) => Bind k (Term d g (a :: SYN k)) t cont r where
  {-# INLINE (>>=) #-}
  (>>=) = bindTerm @k @t

-- | A bind of a term, by its pattern. A variable pattern binds a new variable, so that the right
-- hand side is computed once however often the variable is used. The other patterns take the
-- right hand side apart into new variables already.
type BindTerm :: Type -> Type -> Type -> Type -> Type -> Constraint
class BindTerm k t m cont r where
  bindTerm :: m -> (t -> cont) -> r

-- The instances are incoherent, as for patterns: a variable pattern's type is often still unknown
-- when the instance is chosen.

instance
  {-# INCOHERENT #-}
  (Monoidal k, Binds d r a b t cont, Merge r g, r' ~ Term d (Union r g) b)
  => BindTerm k t (Term d g (a :: SYN k)) cont r'
  where
  {-# INLINE bindTerm #-}
  bindTerm (MkTerm m) k = withCtxOb @r (MkTerm (bound @d @r @a @b k . (ctxOb @r M.** m) . merge @r @g))

instance {-# INCOHERENT #-} (BindPat k (Term d g a) (x, y) cont r) => BindTerm k (x, y) (Term d g (a :: SYN k)) cont r where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat k (Term d g a) (x, y, z) cont r)
  => BindTerm k (x, y, z) (Term d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat k (Term d g a) (w, x, y, z) cont r)
  => BindTerm k (w, x, y, z) (Term d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance {-# INCOHERENT #-} (BindPat k (Term d g a) () cont r) => BindTerm k () (Term d g (a :: SYN k)) cont r where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

-- | A computation on the right hand side runs first, and the rest of the block is negative.
instance
  ( Dialogue k
  , KnownObj y
  , Merge g r
  , TyOf @k cont ~ Not y
  , Binds d r a (Not y) t cont
  , r' ~ Term d (Union g r) (Not y)
  )
  => Bind k (Term d g (Not (Not a))) t cont r'
  where
  {-# INLINE (>>=) #-}
  m >>= k = runUp @d @g @r @a @y m (bound @d @r @a @(Not y) k)

-- | A term on the right hand side taken apart by the pattern of the continuation. The types of the
-- continuation and the result are matched with equalities, so that the instance is chosen as soon
-- as the right hand side is known.
type BindPat :: Type -> Type -> Type -> Type -> Type -> Constraint
class BindPat k m t cont r | m -> k where
  bindPat :: m -> (t -> cont) -> r

instance
  ( cont ~ Term (d + PSize t) (CtxOf @k cont) (TyOf @k cont)
  , r ~ Term d gr (TyOf @k cont)
  , Pat k t d g a (CtxOf @k cont) (TyOf @k cont) gr
  )
  => BindPat k (Term d g (a :: SYN k)) t cont r
  where
  {-# INLINE bindPat #-}
  bindPat = pat @k @t @d @g @a @(CtxOf @k cont) @(TyOf @k cont) @gr

-- | The statement of a @rec@ block, whose continuation is its 'return'.
instance
  (Bind k (Term d g a) t cont r', r ~ Ret tt r')
  => Bind k (Term d g (a :: SYN k)) t (Ret tt cont) r
  where
  {-# INLINE (>>=) #-}
  x >>= k = Ret (x >>= \p -> unRet (k p))

-- | The body of a @rec@ block, tagged with the tuple of its variables. GHC's translation passes
-- that tuple to both 'return' and 'mfix', and this tag is what makes them the same.
type Ret :: Type -> Type -> Type
newtype Ret t x = Ret x

unRet :: Ret t x -> x
unRet (Ret x) = x

-- | A pattern: a variable, @()@, or a pair of patterns. A triple or quadruple stands for pairs
-- nested to the left, as @a ':**' b ':**' c@ is: @(x, y, z)@ is @((x, y), z)@. Binding it at depth
-- @d@ to a term with context @g@ and type @a@, with a continuation with context @g'@ and type @c@,
-- gives a term with context @gr@, which each instance fixes. A pair or @()@ at a computation,
-- @'Up' a@, runs it and matches its value, so @c@ is then negative.
type Pat :: forall k -> Type -> Nat -> Ctx k -> SYN k -> Ctx k -> SYN k -> Ctx k -> Constraint
class Pat k t d g a g' c gr where
  pat :: Term d g a -> (t -> Term (d + PSize t) g' c) -> Term d gr c

-- | The number of variables a pattern binds on the way, and so the depth it adds.
type PSize :: Type -> Nat
type family PSize t where
  PSize (x, y) = 2 + PSize x + PSize y
  PSize (x, y, z) = PSize ((x, y), z)
  PSize (w, x, y, z) = PSize (((w, x), y), z)
  PSize t = 0

-- The generic instances are incoherent: a variable pattern's type is often still unknown when the
-- instance is chosen, and a pair pattern's type is always a pair by then. The instances at a
-- computation are more specific, so they win once the type is known to be an 'Up'.

-- | The pattern @()@ at a computation of the unit runs it.
instance
  (Dialogue k, KnownObj y, c ~ Not y, Merge g g', gr ~ Union g g')
  => Pat k () d g (Not (Not I) :: SYN k) g' c gr
  where
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
  , Pat k (x, y') d '[ '(d, a)] a g' c gp
  , BindVar d a gp r
  , Merge g r
  , gr ~ Union g r
  )
  => Pat k (x, y') d g (Not (Not a) :: SYN k) g' c gr
  where
  {-# INLINE pat #-}
  pat m k = case pat @k @(x, y') @d @'[ '(d, a)] @a @g' @c @gp (var @d @a @d) k of
    MkTerm body -> runUp @d @g @r @a @y m (body . bindVar @d @a @gp @r)

-- | The pattern @()@ uses up a term of the unit type.
instance
  {-# INCOHERENT #-}
  (Monoidal k, a ~ I, KnownObj c, Merge g g', gr ~ Union g g')
  => Pat k () d g (a :: SYN k) g' c gr
  where
  {-# INLINE pat #-}
  pat (MkTerm u) k = case k () of
    MkTerm t -> withSynOb @c (MkTerm (leftUnitor @k @(Interp c) . (u M.** t) . merge @g @g'))

-- | A variable pattern names the right hand side, which is always a variable. If the body does not
-- use it, the binder discards it.
instance {-# INCOHERENT #-} (t ~ Term (DepthOf t) g a, gr ~ g') => Pat k t d g a g' c gr where
  {-# INLINE pat #-}
  pat x k = k (recast x)

instance
  {-# INCOHERENT #-}
  ( Monoidal k
  , a ~ (a1 :** a2)
  , KnownObj a1
  , KnownObj a2
  , Pat k y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g' c gy
  , Pat k x (d + 2) '[ '(d, a1)] a1 gy c gxy
  , d + 2 + PSize x + PSize y ~ d + PSize (x, y)
  , BindVar (d + 1) a2 gxy r1
  , BindVar d a1 r1 r
  , Merge r g
  , gr ~ Union r g
  )
  => Pat k (x, y) d g (a :: SYN k) g' c gr
  where
  {-# INLINE pat #-}
  pat s k =
    split @d @g @gxy @r1 @r
      s
      ( \a b ->
          pat @k @x @(d + 2) @'[ '(d, a1)] @a1 @gy @c @gxy
            a
            (\px -> pat @k @y @(d + 2 + PSize x) @'[ '(d + 1, a2)] @a2 @g' @c @gy b (\py -> k (px, py)))
      )

instance {-# INCOHERENT #-} (Pat k ((x, y), z) d g a g' c gr) => Pat k (x, y, z) d g a g' c gr where
  {-# INLINE pat #-}
  pat s k = pat @k @((x, y), z) @d @g @a @g' @c @gr s (\((px, py), pz) -> k (px, py, pz))

instance {-# INCOHERENT #-} (Pat k (((w, x), y), z) d g a g' c gr) => Pat k (w, x, y, z) d g a g' c gr where
  {-# INLINE pat #-}
  pat s k = pat @k @(((w, x), y), z) @d @g @a @g' @c @gr s (\(((pw, px), py), pz) -> k (pw, px, py, pz))

-- | The variables of a @rec@ block, as GHC tuples them up.
type RecVars :: Type -> Type -> Constraint
class RecVars k t | t -> k where
  type Vars k t :: Ctx k
  recVars :: t

instance (Monoidal k, KnownObj (a :: SYN k)) => RecVars k (Term d '[ '(n, a)] a) where
  {-# INLINE recVars #-}
  type Vars k (Term d '[ '(n, a)] a) = '[ '(n, a)]
  recVars = var @n @a

instance (RecVars k x, RecVars k y) => RecVars k (x, y) where
  {-# INLINE recVars #-}
  type Vars k (x, y) = Union (Vars k x) (Vars k y)
  recVars = (recVars, recVars)

instance (RecVars k x, RecVars k y, RecVars k z) => RecVars k (x, y, z) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z) = Union (Vars k x) (Vars k (y, z))
  recVars = (recVars, recVars, recVars)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w) => RecVars k (x, y, z, w) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w) = Union (Vars k x) (Vars k (y, z, w))
  recVars = (recVars, recVars, recVars, recVars)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v) => RecVars k (x, y, z, w, v) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w, v) = Union (Vars k x) (Vars k (y, z, w, v))
  recVars = (recVars, recVars, recVars, recVars, recVars)

instance
  (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v, RecVars k u)
  => RecVars k (x, y, z, w, v, u)
  where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w, v, u) = Union (Vars k x) (Vars k (y, z, w, v, u))
  recVars = (recVars, recVars, recVars, recVars, recVars, recVars)

-- | The variables of a @rec@ block again, at a depth of their own: the rest of the block uses them
-- deeper than the block did. It is asked for both ways, so that what is known about the variables
-- on either side of the block determines the other.
type AnyDepth :: Type -> Type -> Constraint
class AnyDepth t t'

instance (t' ~ Term d' g a) => AnyDepth (Term d g a) t'

instance (AnyDepth x x', AnyDepth y y', t' ~ (x', y')) => AnyDepth (x, y) t'

instance (AnyDepth x x', AnyDepth y y', AnyDepth z z', t' ~ (x', y', z')) => AnyDepth (x, y, z) t'

instance (AnyDepth x x', AnyDepth y y', AnyDepth z z', AnyDepth w w', t' ~ (x', y', z', w')) => AnyDepth (x, y, z, w) t'

instance
  (AnyDepth x x', AnyDepth y y', AnyDepth z z', AnyDepth w w', AnyDepth v v', t' ~ (x', y', z', w', v'))
  => AnyDepth (x, y, z, w, v) t'

instance
  ( AnyDepth x x'
  , AnyDepth y y'
  , AnyDepth z z'
  , AnyDepth w w'
  , AnyDepth v v'
  , AnyDepth u u'
  , t' ~ (x', y', z', w', v', u')
  )
  => AnyDepth (x, y, z, w, v, u) t'

-- | The end of a @rec@ block: all its variables, as the tensor of their context.
{-# INLINE return #-}
return
  :: forall k t d. (Monoidal k, RecVars k t, KnownCtx (Vars k t)) => t -> Ret t (Term d (Vars k t) (Mul (Vars k t)))
return _ = Ret (MkTerm (ctxOb @(Vars k t)))

-- | A @rec@ block before tracing: its body, from its context @g@ to all its variables. Which of them
-- are fed back and which are passed on is only known with the rest of the block, see the 'Bind'
-- instance.
type Rec :: forall {k}. Nat -> Type -> Ctx k -> Type
data Rec d t g where
  Rec :: forall {k} d t (g :: Ctx k). (Interp (Mul g) ~> Interp (Mul (Vars k t))) -> Rec d t g

-- | The body of a @rec@ block, to be traced by the bind after it.
{-# INLINE mfix #-}
mfix :: forall {k} t d (g :: Ctx k). (RecVars k t) => (t -> Ret t (Term d g (Mul (Vars k t)))) -> Rec d t g
mfix f = case unRet (f recVars) of MkTerm body -> Rec body

-- | The rest of the @do@ block after a @rec@ block, which traces it. The variables of the block
-- that the block itself uses are fed back, the ones the rest uses are passed on, a variable that
-- both use is copied, and one that neither uses is discarded. The rest gets the variables anew,
-- with the same ids, so that it can use them at its own depth.
instance
  ( TracedMonoidal k
  , RecVars k t
  , AnyDepth t t'
  , AnyDepth t' t
  , RecVars k t'
  , cont ~ Term (HeadId (Vars k t) + 1) (CtxOf @k cont) (TyOf @k cont)
  , r ~ Term d (Union (Minus (CtxOf @k cont) (Vars k t)) (Minus g (Vars k t))) (TyOf @k cont)
  , Unmerge (Inter g (Vars k t)) (Minus g (Vars k t))
  , Union (Inter g (Vars k t)) (Minus g (Vars k t)) ~ g
  , Thin (Vars k t) (Union (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)))
  , Merge (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t))
  , Merge (Minus (CtxOf @k cont) (Vars k t)) (Minus g (Vars k t))
  , Unmerge (Minus (CtxOf @k cont) (Vars k t)) (Inter (CtxOf @k cont) (Vars k t))
  , Union (Minus (CtxOf @k cont) (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)) ~ CtxOf @k cont
  )
  => Bind k (Rec d t (g :: Ctx k)) t' cont r
  where
  {-# INLINE (>>=) #-}
  Rec body >>= k = case k (recVars @k @t') of
    MkTerm rest ->
      withCtxOb @(Minus (CtxOf @k cont) (Vars k t))
        ( withCtxOb @(Inter g (Vars k t))
            ( withCtxOb @(Minus g (Vars k t))
                ( withCtxOb @(Inter (CtxOf @k cont) (Vars k t))
                    ( MkTerm
                        ( rest
                            . unmerge @(Minus (CtxOf @k cont) (Vars k t)) @(Inter (CtxOf @k cont) (Vars k t))
                            . ( ctxOb @(Minus (CtxOf @k cont) (Vars k t))
                                  M.** coact
                                    @Tensor
                                    @(~>)
                                    @(Interp (Mul (Inter g (Vars k t))))
                                    @(Interp (Mul (Minus g (Vars k t))))
                                    @(Interp (Mul (Inter (CtxOf @k cont) (Vars k t))))
                                    ( merge @(Inter g (Vars k t)) @(Inter (CtxOf @k cont) (Vars k t))
                                        . thin @(Vars k t) @(Union (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)))
                                        . body
                                        . unmerge @(Inter g (Vars k t)) @(Minus g (Vars k t))
                                    )
                              )
                            . merge @(Minus (CtxOf @k cont) (Vars k t)) @(Minus g (Vars k t))
                        )
                    )
                )
            )
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

type HeadId :: forall {k}. Ctx k -> Nat
type family HeadId g where
  HeadId ('(n, a) ': g) = n

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
  caseOf bc (\b -> inl (a ** b)) (\c -> inr (a ** c))

-- | Swap a coproduct, with nothing to share.
--
-- >>> import Prelude (Bool (..), Either (..), Int)
-- >>> swapEitherT @Int @Bool (Left 1)
-- Right 1
swapEitherT :: forall {k} (a :: k) b. (Distributive k, SymMonoidal k, Ob a, Ob b) => a || b ~> b || a
swapEitherT = toSMC @(F a :|| F b) \x -> caseOf x (\a -> inr a) (\b -> inl b)

-- | A pair both as it is and swapped: the second alternative takes the pair apart.
--
-- >>> import Prelude (Bool (..), Int)
-- >>> bothWaysT @Int @Bool (1, True)
-- ((1,True),(True,1))
bothWaysT
  :: forall {k} (a :: k) b. (SymMonoidal k, HasBinaryProducts k, Ob a, Ob b) => a ** b ~> (a ** b) && (b ** a)
bothWaysT = toSMC @(F a :** F b) \p -> with p (split p \x y -> y ** x)

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

-- | Composition in index notation, as matrix multiplication: the entry at @i@ and @k@ is the sum over
-- @j@ of the entries of @f@ and @g@. It is @g . f@.
matMulT :: forall {k} (a :: k) b c. (SymMonoidal k, Frobenius b, Frobenius c, Ob a) => (a ~> b) -> (b ~> c) -> a ~> c
matMulT f g = toSMC @(F a) \i -> sumOver @(F c) \k -> sumOver @(F b) \j ->
  delta (lift f i) j *^ delta (lift g j) k *^ k

-- | The trace in index notation: the sum of the diagonal entries.
traceIdxT :: forall {k} (a :: k). (SymMonoidal k, Frobenius a) => (a ~> a) -> Unit ~> (Unit :: k)
traceIdxT f = toSMC @I \() -> sumOver @(F a) \i -> delta (lift f i) i

-- | The entrywise product of two morphisms: two boxes that produce the same index.
hadamardT :: forall {k} (a :: k) b. (SymMonoidal k, Frobenius a, Frobenius b) => (a ~> b) -> (a ~> b) -> a ~> b
hadamardT f g = toSMC @(F a) \i -> sumOver @(F b) \j ->
  delta (lift f i) j *^ delta (lift g i) j *^ j

-- | The snake on the dual: join the input with the first end of a new pair, and continue with the
-- second. Here the wires meet in the order they come, so no swap is needed.
snakeDualT :: forall {k} (a :: k). (CompactClosed k, Ob a) => Dual a ~> Dual a
snakeDualT = toSMC @(Not (F a)) \x -> Proarrow.Tools.SMC.do
  (a, a') <- produce
  () <- annihilate x a
  a'
