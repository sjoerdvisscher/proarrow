-- | A HOAS front end for building morphisms in any symmetric monoidal category, the
-- resource-aware counterpart of "Proarrow.Tools.CCC", which grows with the structure of the target: traces,
-- duals, additives, and the polarised System L reading of inputs and outputs in a dialogue
-- category. A 'Term' is indexed by its context, the variables it uses, so a variable is the
-- identity on its own type. Terms combine by merging their contexts, which reorders wires. A
-- variable used exactly once needs nothing more. One that two terms both use is copied, which needs
-- a 'Proarrow.Monoid.CocommutativeComonoid' on its type, and one that its binder's body does not use is discarded,
-- which needs a 'Proarrow.Monoid.Comonoid'. So the types ask for copying and discarding only where a term does it.
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
  ) where

import Proarrow.Tools.SMC.Internal.Additive
import Proarrow.Tools.SMC.Internal.Closed
import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Dialogue
import Proarrow.Tools.SMC.Internal.Do
import Proarrow.Tools.SMC.Internal.Frobenius
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

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

-- $index
-- Index notation, as in Einstein summation, for a category whose index types are special
-- commutative Frobenius algebras, such as a hypergraph category. An index is a variable whose type
-- is such an object. Using an index more than once copies it, so every use sees the same value,
-- and 'sumOver' binds an index that is summed over. 'delta' says that two wires carry the same
-- value, which is how a morphism lifted onto an index is tied to another index: in "Proarrow.Category.Instance.Mat",
-- @'delta' ('lift' f i) j@ is the entry of @f@ at @i@ and @j@. A term of type 'I' is a scalar, and
-- @(*^)@ and @(^*)@ multiply a term by one. An output index is a summed index that the term also
-- returns, so matrix multiplication is 'Proarrow.Tools.SMC.Examples.matMulT':
--
-- > \i -> sumOver \k -> sumOver \j -> delta (lift f i) j *^ delta (lift g j) k *^ k
--
-- What the sum is depends on the category: in 'Proarrow.Category.Instance.Mat.Mat' it is the sum
-- of numbers, in 'Proarrow.Category.Instance.FinRel.FinRel' it is "there is", and in the diagram
-- categories it is a wire with no end on the boundary.

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

-- $additives
-- The additives share their context between alternatives, of which only one is used, so a
-- variable that several alternatives use is not copied. One that an alternative does not use is
-- discarded there.
