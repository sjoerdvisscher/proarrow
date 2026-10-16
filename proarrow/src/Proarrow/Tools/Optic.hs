{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Compile resource-aware SMC programs of optics to forward/backward computations.
-- A wire @'(a, da)@ carries its forward and backward objects. 'optic' and 'opticLegs'
-- expand each primitive to two boxes joined by its residual; 'runOptics' connects them
-- by graph substitution and reads the computation into the target symmetric monoidal category.
-- No trace or Frobenius structure is required of the target.
--
-- For example, an SMC program on @Wires '[ '(Double, Double)]@ can compose the
-- primitive @opticLegs \@Double (\x -> (x, x*x)) (\(x, dy) -> 2*x*dy)@ with
-- @opticLegs \@Double (\x -> (cos x, sin x)) (uncurry (*))@. Applying 'runOptics'
-- gives @(x, dy) -> (sin (x*x), 2*x*cos (x*x)*dy)@. A primitive with several output
-- wires supports an ordinary SMC tuple pattern. An explicit duplication optic can
-- copy a forward value and add its two cotangents on the backward pass.
--
-- This is the optic translation in §10 of Wilson and Zanasi,
-- <https://arxiv.org/abs/2305.01041 Data-Parallel Algorithms for String Diagrams>.
-- The source program may compose, tensor and permute its wires. Copying, discarding,
-- merging and feedback are rejected when their translated wiring needs stronger structure.
module Proarrow.Tools.Optic (OPTICS, Forward, Backward, optic, opticLegs, runOptics) where

import Data.Map.Strict qualified as M
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.FinHask (FinHask (..))
import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , Boxes (..)
  , OPENHG
  , Port (..)
  , Prim
  , SomeHypergraph (..)
  , SomeSort
  , SortList
  , SortOb
  , Sorts
  , WireSorts
  , Wires
  , box
  , permutations
  , reifySorts
  , simplify
  , someArrow
  , sortList
  , sorts
  , unsafeOpenHypergraph
  , unsafePrim
  , unsafeSubstituteWith
  )
import Proarrow.Category.Instance.Product (Fst, Snd)
import Proarrow.Category.Instance.Sub (Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, Tensor)
import Proarrow.Category.Monoidal.Strictified
  ( Fold
  , Strictified (..)
  , concatMany
  , splitMany
  , withIsListOf
  , type (++)
  )
import Proarrow.Core (CategoryOf (..), Kind, Promonad (..), obj)
import Proarrow.Functor (FunctorForRep (type (@)))
import Proarrow.Object (ListOf (..), SomeOf (..), withKnownAppend, withKnownListOf, pattern Objs)
import Proarrow.Optic (ExOptic, Optic, withLegs)
import Proarrow.Optic.Action (ActFl (..))

-- | Graphs of typed optic primitives. Build boxes with 'optic' or 'opticLegs'; reattaching
-- their hidden labels to other sorts breaks the type agreement used by 'runOptics'.
type OPTICS :: Kind -> Kind
type OPTICS k = OPENHG (k, k) (OpticPrim k)

newtype OpticPrim k = OpticPrim (SomeHypergraph k (Prim k))

-- | The forward objects of a list of optic wires, in boundary order.
type Forward :: [(k, k)] -> [k]
type family Forward xs where
  Forward '[] = '[]
  Forward ('(a, da) ': xs) = a ': Forward xs

-- | The backward objects of a list of optic wires, in boundary order.
type Backward :: [(k, k)] -> [k]
type family Backward xs where
  Backward '[] = '[]
  Backward ('(a, da) ': xs) = da ': Backward xs

-- | A primitive from an existing tensor-action optic, in any encoding supported by 'withLegs'.
optic
  :: forall {k} c (xs :: [(k, k)]) ys
   . ( SymMonoidal k
     , SortList xs
     , SortList ys
     , (Ob (Fold (Forward ys)), Ob (Fold (Backward ys))) => c (ExOptic (ActFl Tensor) (Fold (Forward ys)) (Fold (Backward ys)))
     )
  => Optic c (Fold (Forward xs)) (Fold (Backward xs)) (Fold (Forward ys)) (Fold (Backward ys))
  -> (Wires xs :: OPTICS k) ~> Wires ys
optic o@Objs =
  withLegs @(ActFl Tensor) o \l r -> withActP @Tensor l r \ @m f g -> opticLegs @m @xs @ys f g

-- | A primitive from its two legs, with residual @m@. The residual is produced once by
-- the forward leg and consumed by the backward leg; it needs no comonoid structure.
-- The forward and backward lists of ports are folded with the target's tensor.
opticLegs
  :: forall {k} (m :: k) (xs :: [(k, k)]) ys
   . (SymMonoidal k, Ob m, SortList xs, SortList ys)
  => (Fold (Forward xs) ~> m ** Fold (Forward ys))
  -> (m ** Fold (Backward ys) ~> Fold (Backward xs))
  -> (Wires xs :: OPTICS k) ~> Wires ys
opticLegs f g = withHalves (sorts @_ @xs) $
  withHalves (sorts @_ @ys) $
    case (concatMany @(Forward xs), splitMany @(Forward ys), concatMany @(Backward ys), splitMany @(Backward xs)) of
      (joinForward@Objs, splitForward@Objs, joinBackward@Objs, splitBackward@Objs) ->
        let inputs = concatMap expand (sortList @_ @xs)
            outputs = concatMap expand (sortList @_ @ys)
            ni = length inputs
            no = length outputs
            residual = ni + no
            forward =
              (obj @'[m] ** splitForward) . Str @'[Fold (Forward xs)] @'[m, Fold (Forward ys)] f . joinForward
            backward =
              splitBackward
                . Str @'[m, Fold (Backward ys)] @'[Fold (Backward xs)] g
                . (obj @'[m] ** joinBackward)
            boxes =
              [ Box (unsafePrim (someArrow forward)) [0, 2 .. ni - 1] (residual : [ni, ni + 2 .. residual - 1])
              , Box (unsafePrim (someArrow backward)) (residual : [ni + 1, ni + 3 .. residual - 1]) [1, 3 .. ni - 1]
              ]
            replacement = reifySorts inputs \ @as -> reifySorts outputs \ @bs ->
              SomeHypergraph
                (unsafeOpenHypergraph @(Prim k) @as @bs (inputs ++ outputs ++ [Some @m]) [0 .. ni - 1] [ni .. residual - 1] boxes)
        in box (OpticPrim replacement)

-- | Expand the primitives, move the external backward wires to the other boundary, and
-- read back using 'permutations'. The inputs are the forward source and backward target;
-- the outputs are the forward target and backward source. Empty boundaries fold to the unit.
runOptics
  :: forall {k} (xs :: [(k, k)]) ys
   . (SymMonoidal k)
  => (Wires xs :: OPTICS k) ~> Wires ys
  -> Either String ((Fold (Forward xs) ** Fold (Backward ys)) ~> (Fold (Forward ys) ** Fold (Backward xs)))
runOptics graph@Objs =
  withHalves (sorts @_ @xs) $
    withHalves (sorts @_ @ys) $
      withKnownAppend @SortOb @(Forward xs) @(Backward ys) $
        withKnownAppend @SortOb @(Forward ys) @(Backward xs) $ do
          SomeHypergraph (DecCospan @c (Sub (FinHask ins)) (Sub (FinHask outs)) (Boxes boxes)) <-
            unsafeSubstituteWith expand (\(OpticPrim g) -> g) graph
          let unPort (Port i) = i
              inputs = map unPort (M.elems ins)
              outputs = map unPort (M.elems outs)
              evenPorts = everyOther
              oddPorts = everyOther . drop 1
              computation =
                unsafeOpenHypergraph @(Prim k)
                  @(Forward xs ++ Backward ys)
                  @(Forward ys ++ Backward xs)
                  (sortList @_ @(WireSorts (DC c)))
                  (evenPorts inputs ++ oddPorts outputs)
                  (evenPorts outputs ++ oddPorts inputs)
                  (map (fmap unPort) boxes)
          result <- simplify permutations computation
          pure $
            unStr
              ((concatMany @(Forward ys) ** concatMany @(Backward xs)) . result . (splitMany @(Forward xs) ** splitMany @(Backward ys)))
  where
    everyOther [] = []
    everyOther (x : rest) = x : everyOther (drop 1 rest)

expand :: (CategoryOf k) => SomeSort (k, k) -> [SomeSort k]
expand (Some @p) = [Some @(Fst @ p), Some @(Snd @ p)]

withHalves
  :: forall {k} xs r
   . (CategoryOf k)
  => Sorts (xs :: [(k, k)])
  -> ( ( SortList (Forward xs)
       , SortList (Backward xs)
       , Ob (Forward xs)
       , Ob (Backward xs)
       )
       => r
     )
  -> r
withHalves xs k = go xs \as ds ->
  withKnownListOf as $
    withKnownListOf ds $
      withIsListOf as $
        withIsListOf ds k
  where
    go :: Sorts (zs :: [(k, k)]) -> (Sorts (Forward zs) -> Sorts (Backward zs) -> r) -> r
    go Nil next = next Nil Nil
    go (Cons @p rest) next = go rest \as ds -> next (Cons @(Fst @ p) as) (Cons @(Snd @ p) ds)
