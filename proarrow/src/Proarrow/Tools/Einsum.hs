{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Einstein summation with a numpy-style specification, as in @'einsum' \@"ij,jk->ik" a b@, in any
-- hypergraph category. A tensor is a state, @'Tensor' xs@, whose type lists the objects of its
-- indices. Each letter of the specification is an index; the letters of the inputs are matched with
-- the objects of the tensors given, so a letter used with two different objects does not compile,
-- and the result's objects are those of the output letters. Without @->@ the output is, as in
-- numpy, the letters used once, in alphabetical order. A letter may also occur more than once in the
-- output, which copies it.
--
-- The specification is an open hypergraph ("Proarrow.Category.Instance.OpenHypergraph"): a node for
-- each letter, the tensors as boxes, and the output letters as its boundary. It is already in normal
-- form, and the result is its 'Proarrow.Category.Instance.OpenHypergraph.simplify': the tensors
-- one at a time, each letter summed out by a spider as soon as no later tensor has it.
module Proarrow.Tools.Einsum
  ( Tensor
  , einsum
  , Einsum
  , EinsumType
  , Inputs
  , Output
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Constraint, Type)
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (..))
import Data.Type.Bool (type (&&), type (||))
import Data.Type.Equality (type (==))
import GHC.TypeLits (CmpChar, ErrorMessage (..), KnownChar, Symbol, TypeError, UnconsSymbol, charVal)
import GHC.TypeNats (Nat, type (+))
import Prelude (Bool (..), Char, Maybe (..), Ordering (..), type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , SIMPLIFY
  , SomeArrow (..)
  , SortList
  , Wires
  , simplify
  , someArrow
  , unsafeOpenHypergraph
  , unsafePrim
  )
import Proarrow.Category.Instance.Product (Fst, Snd)
import Proarrow.Category.Monoidal (State)
import Proarrow.Category.Monoidal.Hypergraph (Hypergraph, Sized)
import Proarrow.Category.Monoidal.Strictified (Fold, type (++))
import Proarrow.Core (CategoryOf (..), Kind)
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object (KnownListOf (..), mapListOf, someOfList)

-- | A tensor with indices of the given objects: a state of their tensor, as a morphism of
-- 'Strictified' from @'[]@.
type Tensor :: forall k. [k] -> Type
type Tensor xs = State xs

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
  ParseArrow _ _ = TypeError (Text "Proarrow.Tools.Einsum: expected > after - in the specification")

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
type Env :: Kind -> Kind
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
    TypeError (Text "Proarrow.Tools.Einsum: " :<>: ShowType l :<>: Text " is not a letter, so it cannot be an index")

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
      ( Text "Proarrow.Tools.Einsum: the tensor with indices "
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
      ( Text "Proarrow.Tools.Einsum: the index "
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
      (Text "Proarrow.Tools.Einsum: the output letter " :<>: ShowType c :<>: Text " is not an index of any input")

-- | The objects of the given letters.
type Objs :: forall k. [Char] -> Env k -> [k]
type family Objs ls env where
  Objs '[] env = '[]
  Objs (c ': ls) env = Lookup c env ': Objs ls env

type Len :: [a] -> Nat
type family Len xs where
  Len '[] = 0
  Len (x ': xs) = 1 + Len xs

-- The network

-- | The letters as a value.
type KnownChars :: [Char] -> Constraint
type KnownChars ls = KnownListOf KnownChar ls

chars :: forall ls. (KnownChars ls) => [Char]
chars = mapListOf @KnownChar (\ @c -> charVal (Proxy @c)) (listOf @KnownChar @ls)

-- | The open hypergraph of a specification: a node for each letter, of the sort of its object, a box
-- for each tensor with an output for each of its letters, and the output letters as the boundary.
-- The type checker has matched the letters with the objects of the tensors and of the output, so
-- the hypergraph needs no checks.
network
  :: forall {k} (os :: [k])
   . (SortList os)
  => [([Char], SomeArrow k)]
  -> [Char]
  -> Wires '[] ~> (Wires os :: SIMPLIFY k)
network tensors out =
  unsafeOpenHypergraph
    (P.fmap (sortOfLetter M.!) letters)
    []
    (P.fmap (index M.!) out)
    [Box (unsafePrim t) [] (P.fmap (index M.!) ls) | (ls, t) <- tensors]
  where
    -- the letters in the order they first appear, with their sorts
    letters = nubOrd (P.concatMap P.fst tensors)
    sortOfLetter = M.fromList [(l, x) | (ls, SomeArrow _ ys _) <- tensors, (l, x) <- P.zip ls (someOfList ys)]
    index = M.fromList (P.zip letters [0 ..])

-- Einsum

-- | Collect the tensors of the inputs, then sum.
type Einsum :: forall {k}. [[Char]] -> [Char] -> [([Char], [k])] -> Type -> Constraint
class Einsum ins out (ts :: [([Char], [k])]) r where
  collect :: [([Char], SomeArrow k)] -> r

instance
  (r ~ (Tensor xs -> r'), KnownChars ls, SortList xs, Einsum ins out ('(ls, xs) ': ts) r')
  => Einsum (ls ': ins) out (ts :: [([Char], [k])]) r
  where
  collect acc t = collect @ins @out @('(ls, xs) ': ts) ((chars @ls, someArrow t) : acc)

-- The tensors are the boxes of an open hypergraph, which is read back with each box its tensor.
instance
  ( env ~ BindAll (Reverse ts) '[]
  , Check ts out env
  , Hypergraph k
  , Sized k
  , os ~ Objs out env
  , r ~ Tensor os
  , SortList os
  , KnownChars out
  )
  => Einsum '[] out (ts :: [([Char], [k])]) r
  where
  collect acc = simplify (network @os (P.reverse acc) (chars @out))

-- | Einstein summation: @einsum \@"ij,jk->ik" a b@ is the tensor with entries the sums over @j@ of
-- the products of the entries of @a@ and @b@. The tensors are given after the specification, one for
-- each input, and the result's type follows from theirs.
einsum :: forall {k} (s :: Symbol) r. (Einsum (Inputs s) (Output s) ('[] :: [([Char], [k])]) r) => r
einsum = collect @(Inputs s) @(Output s) @('[] :: [([Char], [k])]) []

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
