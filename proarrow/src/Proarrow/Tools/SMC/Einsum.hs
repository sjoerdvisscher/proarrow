{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Einstein summation with a numpy-style specification, as in @'einsum' \@"ij,jk->ik" a b@, in any
-- hypergraph category. A tensor is a state, @'Tensor' xs@, whose type lists the objects of its
-- indices. Each letter of the specification is an index; the letters of the inputs are matched with
-- the objects of the tensors given, so a letter used with two different objects does not compile,
-- and the result's objects are those of the output letters. Without @->@ the output is, as in
-- numpy, the letters used once, in alphabetical order. Every index is summed over, and an index the
-- output has is also returned, so the result is computed by the index notation of
-- "Proarrow.Tools.SMC". A letter may also occur more than once in the output, which copies it.
module Proarrow.Tools.SMC.Einsum
  ( Tensor
  , einsum
  , Einsum
  , EinsumType
  , Inputs
  , Output
  ) where

import Data.Kind (Constraint, Type)
import Data.Type.Bool (type (&&), type (||))
import Data.Type.Equality (type (==))
import GHC.TypeLits (CmpChar, ErrorMessage (..), Symbol, TypeError, UnconsSymbol)
import GHC.TypeNats (Nat, type (+))
import Prelude (Bool (..), Char, Maybe (..), Ordering (..), type (~))

import Proarrow.Category.Instance.Product (Fst, Snd)
import Proarrow.Category.Monoidal (Monoidal (..), State)
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, Hypergraph)
import Proarrow.Category.Monoidal.Strictified (Fold, IsList, Strictified (..), withObFold, type (++))
import Proarrow.Core (CategoryOf (..))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Frobenius
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

-- | A tensor with indices of the given objects: a state of their tensor, as a morphism of
-- 'Strictified' from @'[]@.
type Tensor :: forall k. [k] -> Type
type Tensor xs = State xs

-- Unlike the rest of Proarrow.Tools.SMC, nothing here is INLINE: inlining the generated term made
-- optimised compilation grow much faster with the number of inputs, and the result ran slower, as
-- the parts that do not depend on the tensors were no longer shared between calls.

-- The specification

-- | A specification parsed into the letters of each input and of the output.
type Parse :: Symbol -> ([[Char]], [Char])
type Parse s = ParseInputs (UnconsSymbol s) '[] '[]

-- | The letters of each input.
type Inputs :: Symbol -> [[Char]]
type Inputs s = Fst @ Parse s

-- | The letters of the output.
type Output :: Symbol -> [Char]
type Output s = Snd @ Parse s

-- the letters of the current input, reversed, and the inputs before it, reversed
type ParseInputs :: Maybe (Char, Symbol) -> [Char] -> [[Char]] -> ([[Char]], [Char])
type family ParseInputs m cur acc where
  ParseInputs 'Nothing cur acc = Implicit (Finish cur acc)
  ParseInputs ('Just '( ',', s)) cur acc = ParseInputs (UnconsSymbol s) '[] (Reverse cur ': acc)
  ParseInputs ('Just '( ' ', s)) cur acc = ParseInputs (UnconsSymbol s) cur acc
  ParseInputs ('Just '( '-', s)) cur acc = ParseArrow (UnconsSymbol s) (Finish cur acc)
  ParseInputs ('Just '(c, s)) cur acc = ParseInputs (UnconsSymbol s) (c ': cur) acc

-- the inputs, with the letters of the last one
type Finish :: [Char] -> [[Char]] -> [[Char]]
type Finish cur acc = Reverse (Reverse cur ': acc)

type ParseArrow :: Maybe (Char, Symbol) -> [[Char]] -> ([[Char]], [Char])
type family ParseArrow m ins where
  ParseArrow ('Just '( '>', s)) ins = '(ins, ParseOutput (UnconsSymbol s) '[])
  ParseArrow _ _ = TypeError (Text "Proarrow.Tools.SMC.Einsum: expected > after - in the specification")

-- | The inputs with numpy's implicit output: the letters used once, in alphabetical order.
type Implicit :: [[Char]] -> ([[Char]], [Char])
type Implicit ins = '(ins, Sort (Once (Fold ins) (Fold ins)))

-- the letters of the first list that occur once in the second
type Once :: [Char] -> [Char] -> [Char]
type family Once cs all where
  Once '[] all = '[]
  Once (c ': cs) all = OnceIf (Count c all) c (Once cs all)

type OnceIf :: Nat -> Char -> [Char] -> [Char]
type family OnceIf n c cs where
  OnceIf 1 c cs = c ': cs
  OnceIf _ c cs = cs

type Count :: Char -> [Char] -> Nat
type family Count c cs where
  Count c '[] = 0
  Count c (c ': cs) = 1 + Count c cs
  Count c (d ': cs) = Count c cs

type Sort :: [Char] -> [Char]
type family Sort cs where
  Sort '[] = '[]
  Sort (c ': cs) = InsertSorted c (Sort cs)

type InsertSorted :: Char -> [Char] -> [Char]
type family InsertSorted c cs where
  InsertSorted c '[] = '[c]
  InsertSorted c (d ': ds) = InsertOrd (CmpChar c d) c d ds

type InsertOrd :: Ordering -> Char -> Char -> [Char] -> [Char]
type family InsertOrd o c d ds where
  InsertOrd 'GT c d ds = d ': InsertSorted c ds
  InsertOrd _ c d ds = c ': d ': ds

type ParseOutput :: Maybe (Char, Symbol) -> [Char] -> [Char]
type family ParseOutput m cur where
  ParseOutput 'Nothing cur = Reverse cur
  ParseOutput ('Just '( ' ', s)) cur = ParseOutput (UnconsSymbol s) cur
  ParseOutput ('Just '(c, s)) cur = ParseOutput (UnconsSymbol s) (c ': cur)

type Reverse :: [a] -> [a]
type Reverse xs = ReverseOnto xs '[]

type ReverseOnto :: [a] -> [a] -> [a]
type family ReverseOnto xs acc where
  ReverseOnto '[] acc = acc
  ReverseOnto (x ': xs) acc = ReverseOnto xs (x ': acc)

-- The indices

-- | The objects of the indices, by letter, in the order the letters first appear.
type Env :: Type -> Type
type Env k = [(Char, k)]

-- | The letters of the inputs matched with the objects of their tensors.
type BindAll :: forall k. [([Char], [k])] -> Env k -> Env k
type family BindAll ts env where
  BindAll '[] env = env
  BindAll ('(ls, xs) ': ts) env = BindAll ts (Bind ls xs env)

type Bind :: forall k. [Char] -> [k] -> Env k -> Env k
type family Bind ls xs env where
  Bind (c ': ls) (x ': xs) env = Bind ls xs (Insert c x env)
  Bind _ _ env = env

-- a letter already bound keeps its first object; 'Check' reports a second one
type Insert :: forall k. Char -> k -> Env k -> Env k
type family Insert c x env where
  Insert c x '[] = '[ '(c, x)]
  Insert c x ('(c, y) ': env) = '(c, y) ': env
  Insert c x (p ': env) = p ': Insert c x env

-- stuck at a letter no input has, which 'Check' reports
type Lookup :: forall k. Char -> Env k -> k
type family Lookup c env where
  Lookup c ('(c, x) ': env) = x
  Lookup c (p ': env) = Lookup c env

-- | The errors of a specification, reported once: a tensor with a different number of indices than
-- letters, a character that is not a letter, and, when there is neither, a letter used with two
-- objects and an output letter no input has. The other constraints of 'Einsum' get stuck instead
-- of repeating them.
type Check :: forall k. [([Char], [k])] -> [Char] -> Env k -> Constraint
type Check ts out env = Letters (LettersOf ts ++ out) (Arities ts (Agreements ts env, CheckOutput out env))

type LettersOf :: forall k. [([Char], [k])] -> [Char]
type family LettersOf ts where
  LettersOf '[] = '[]
  LettersOf ('(ls, xs) ': ts) = ls ++ LettersOf ts

-- the given constraint, when every index is a letter
type Letters :: [Char] -> Constraint -> Constraint
type family Letters ls c where
  Letters '[] c = c
  Letters (l ': ls) c = LetterIf (IsLetter l) l (Letters ls c)

type LetterIf :: Bool -> Char -> Constraint -> Constraint
type family LetterIf ok l c where
  LetterIf 'True l c = c
  LetterIf 'False l c =
    TypeError (Text "Proarrow.Tools.SMC.Einsum: " :<>: ShowType l :<>: Text " is not a letter, so it cannot be an index")

type IsLetter :: Char -> Bool
type IsLetter c = Within 'a' c 'z' || Within 'A' c 'Z'

-- whether the middle character is between the outer two
type Within :: Char -> Char -> Char -> Bool
type Within lo c hi = NotGT (CmpChar lo c) && NotGT (CmpChar c hi)

type NotGT :: Ordering -> Bool
type family NotGT o where
  NotGT 'GT = 'False
  NotGT _ = 'True

-- the given constraint, when every tensor has as many letters as indices
type Arities :: forall k. [([Char], [k])] -> Constraint -> Constraint
type family Arities ts c where
  Arities '[] c = c
  Arities ('(ls, xs) ': ts) c = ArityError (Len ls == Len xs) ls xs (Arities ts c)

type ArityError :: forall k. Bool -> [Char] -> [k] -> Constraint -> Constraint
type family ArityError ok ls xs c where
  ArityError 'True ls xs c = c
  ArityError 'False ls xs c =
    TypeError
      ( Text "Proarrow.Tools.SMC.Einsum: the tensor with indices "
          :<>: ShowType xs
          :<>: Text " has letters "
          :<>: ShowType ls
      )

type Agreements :: forall k. [([Char], [k])] -> Env k -> Constraint
type family Agreements ts env where
  Agreements '[] env = ()
  Agreements ('(c ': ls, x ': xs) ': ts) env = (Agrees c x env, Agreements ('(ls, xs) ': ts) env)
  Agreements ('(ls, xs) ': ts) env = Agreements ts env

type Agrees :: forall k. Char -> k -> Env k -> Constraint
type family Agrees c x env where
  Agrees c x ('(c, x) ': env) = ()
  Agrees c x ('(c, y) ': env) =
    TypeError
      ( Text "Proarrow.Tools.SMC.Einsum: the index "
          :<>: ShowType c
          :<>: Text " is used with both "
          :<>: ShowType y
          :<>: Text " and "
          :<>: ShowType x
      )
  Agrees c x (p ': env) = Agrees c x env

type CheckOutput :: forall k. [Char] -> Env k -> Constraint
type family CheckOutput out env where
  CheckOutput '[] env = ()
  CheckOutput (c ': out) env = (Bound c env, CheckOutput out env)

type Bound :: forall k. Char -> Env k -> Constraint
type family Bound c env where
  Bound c ('(c, x) ': env) = ()
  Bound c (p ': env) = Bound c env
  Bound c '[] =
    TypeError
      (Text "Proarrow.Tools.SMC.Einsum: the output letter " :<>: ShowType c :<>: Text " is not an index of any input")

-- | The objects of the given letters.
type Objs :: forall k. [Char] -> Env k -> [k]
type family Objs ls env where
  Objs '[] env = '[]
  Objs (c ': ls) env = Lookup c env ': Objs ls env

-- | The id of the variable of a letter, the letters being bound from depth @d@ on.
type IdOf :: forall k. Char -> Env k -> Nat -> Nat
type family IdOf c env d where
  IdOf c ('(c, x) ': env) d = d
  IdOf c (p ': env) d = IdOf c env (d + 1)

type Len :: [a] -> Nat
type family Len xs where
  Len '[] = 0
  Len (x ': xs) = 1 + Len xs

-- | The type expression of a tensor of the given objects, nested as 'Fold' nests them.
type ProdS :: forall k. [k] -> SYN k
type family ProdS xs where
  ProdS '[] = I
  ProdS '[x] = F x
  ProdS (x ': xs) = F x :** ProdS xs

-- Terms

-- | The variables of the given letters, side by side.
type VarsCtx :: forall k. [Char] -> Env k -> Nat -> Ctx k
type family VarsCtx ls env d where
  VarsCtx '[] env d = '[]
  VarsCtx (c ': ls) env d = Union '[ '(IdOf c env d, F (Lookup c env))] (VarsCtx ls env d)

type VarsOf :: forall {k}. [Char] -> Env k -> Nat -> Constraint
class VarsOf ls (env :: Env k) d where
  varsOf :: Term e (VarsCtx ls env d) (ProdS (Objs ls env))

instance (Monoidal k) => VarsOf '[] (env :: Env k) d where
  varsOf = unit

instance (CategoryOf k, KnownObj (F (Lookup c env))) => VarsOf '[c] (env :: Env k) d where
  varsOf = var @(IdOf c env d) @(F (Lookup c env))

instance
  ( Monoidal k
  , KnownObj (F (Lookup c env))
  , VarsOf (c2 ': ls) env d
  , Merge '[ '(IdOf c env d, F (Lookup c env))] (VarsCtx (c2 ': ls) env d)
  )
  => VarsOf (c ': c2 ': ls) (env :: Env k) d
  where
  varsOf = var @(IdOf c env d) @(F (Lookup c env)) ** varsOf @(c2 ': ls) @env @d

-- | The tensors given, with the letters of each.
type Tensors :: forall k. [([Char], [k])] -> Type
data Tensors ts where
  TNil :: Tensors '[]
  TCons :: Tensor xs -> Tensors ts -> Tensors ('(ls, xs) ': ts)

-- | The context of the tensors' factors times a term with context @g@.
type FactorsCtx :: forall k. [([Char], [k])] -> Env k -> Nat -> Ctx k -> Ctx k
type family FactorsCtx ts env d g where
  FactorsCtx '[] env d g = g
  FactorsCtx ('(ls, xs) ': ts) env d g = Union (VarsCtx ls env d) (FactorsCtx ts env d g)

-- | A term multiplied by the delta between each tensor and the tuple of its indices, which is the cap
-- of the Frobenius structure on the tensor of their objects.
type Factors :: forall {k}. [([Char], [k])] -> Env k -> Nat -> Ctx k -> SYN k -> Constraint
class Factors ts (env :: Env k) d g a where
  factors :: Tensors ts -> Term e g a -> Term e (FactorsCtx ts env d g) a

instance Factors '[] (env :: Env k) d g a where
  factors TNil t = t

instance
  ( Hypergraph k
  , Objs ls env ~ xs
  , Interp (ProdS xs) ~ Fold xs
  , KnownObj (ProdS xs)
  , VarsOf ls env d
  , KnownObj a
  , Factors ts env d g a
  , Merge '[] (VarsCtx ls env d)
  , Merge (VarsCtx ls env d) (FactorsCtx ts env d g)
  )
  => Factors ('(ls, xs) ': ts) (env :: Env k) d g a
  where
  factors (TCons (Str t) rest) x =
    withObFold @xs (delta (lift @I @(ProdS xs) t unit) (varsOf @ls @env @d) *^ factors @ts @env @d rest x)

-- | The body with every letter summed over, from depth @d@ on, the body being at depth @b@.
type Sums :: forall {k}. Env k -> Nat -> Nat -> Ctx k -> SYN k -> Ctx k -> Constraint
class Sums (env :: Env k) d b g a r | env d -> b, env d b g a -> r where
  sums :: Term b g a -> Term d r a

instance Sums ('[] :: Env k) d d g a g where
  sums t = t

instance
  ( Monoidal k
  , Frobenius x
  , KnownObj (F x)
  , Sums env (d + 1) b g a r'
  , BindVar d (F x) r' r
  )
  => Sums ('(c, x) ': env :: Env k) d b g a r
  where
  sums body = sumVar @(F x) @d (sums @env @(d + 1) body)

-- Einsum

-- | Collect the tensors of the inputs, then sum.
type Einsum :: forall {k}. [[Char]] -> [Char] -> [([Char], [k])] -> Type -> Constraint
class Einsum ins out (ts :: [([Char], [k])]) r where
  collect :: Tensors ts -> r

instance (r ~ (Tensor xs -> r'), Einsum ins out ('(ls, xs) ': ts) r') => Einsum (ls ': ins) out (ts :: [([Char], [k])]) r where
  collect ts t = collect @ins @out @('(ls, xs) ': ts) (TCons t ts)

instance
  ( env ~ BindAll (Reverse ts) '[]
  , Check ts out env
  , Hypergraph k
  , os ~ Objs out env
  , r ~ Tensor os
  , IsList os
  , Interp (ProdS os) ~ Fold os
  , KnownObj (ProdS os)
  , VarsOf out env 1
  , Factors ts env 1 (VarsCtx out env 1) (ProdS os)
  , Sums env 1 b (FactorsCtx ts env 1 (VarsCtx out env 1)) (ProdS os) '[]
  )
  => Einsum '[] out (ts :: [([Char], [k])]) r
  where
  collect ts = Str (toSMC @I @(ProdS os) \() -> sums @env @1 (factors @ts @env @1 ts (varsOf @out @env @1)))

-- | Einstein summation: @einsum \@"ij,jk->ik" a b@ is the tensor with entries the sums over @j@ of
-- the products of the entries of @a@ and @b@. The tensors are given after the specification, one for
-- each input, and the result's type follows from theirs.
einsum :: forall {k} (s :: Symbol) r. (Einsum (Inputs s) (Output s) ('[] :: [([Char], [k])]) r) => r
einsum = collect @(Inputs s) @(Output s) @('[] :: [([Char], [k])]) TNil

-- | The type of @'einsum' \@s@ applied to tensors with indices of the given objects. Each letter
-- takes the object it is first given, so a letter given two objects is one type variable in every
-- input, as in
-- @'EinsumType' "ij,jk" '[ '[a, b], '[c, d]] = 'Tensor' '[a, b] -> 'Tensor' '[b, d] -> 'Tensor' '[a, d]@.
type EinsumType :: forall k. Symbol -> [[k]] -> Type
type EinsumType s xss = Arrows (Inputs s) (Output s) (BindAll (Zip (Inputs s) xss) '[])

type Zip :: [a] -> [b] -> [(a, b)]
type family Zip as bs where
  Zip (a ': as) (b ': bs) = '(a, b) ': Zip as bs
  Zip _ _ = '[]

type Arrows :: forall k. [[Char]] -> [Char] -> Env k -> Type
type family Arrows ins out env where
  Arrows '[] out env = Tensor (Objs out env)
  Arrows (ls ': ins) out env = Tensor (Objs ls env) -> Arrows ins out env
