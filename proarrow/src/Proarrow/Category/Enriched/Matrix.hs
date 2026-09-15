-- | Matrices valued in an enriching category @v@ that is a type-level quantale -- monoidal, with
-- coproducts and an initial object, like 'Proarrow.Category.Instance.Bool.BOOL' and
-- 'Proarrow.Category.Instance.Cost.COST' -- and indexed by the objects of a kind. Composing enriched
-- profunctors over an enumerable middle category is matrix multiplication ('MatMul'), and the
-- 'Closure' of a @v@-weighted graph, the fixed point of /identity, or one more edge/, is the free
-- @v@-category on it: reachability for @BOOL@, shortest-path distances for @COST@ (Seven Sketches,
-- section 2.5). Everything here lives at the type level; GHC does the computing.
module Proarrow.Category.Enriched.Matrix where

import Data.Kind (Type)
import Data.Type.Nat (Nat (..))

import Proarrow.Category.Enriched (EnrichedProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (Kind, type (+->))

-- | The entries of a @v@-valued matrix, named by a tag type @m@. This generalises 'ProObj' (see 'Pro')
-- to things that are not enriched profunctors: a weighted graph has a matrix but nothing composes in
-- it yet, and so do the intermediate iterates of a 'Closure'. It cannot simply /be/ 'ProObj', since
-- an associated family only gets instances inside class instances, and one for every @v@ would
-- overlap the instance for @Type@.
type Entry :: forall {j} {k}. forall (v :: Kind) -> Type -> k -> j -> v
type family Entry v m (a :: k) (b :: j)

-- | The matrix of an enriched profunctor.
type Pro :: forall {j} {k}. (j +-> k) -> Type
data Pro p

type instance Entry v (Pro (p :: j +-> k)) (a :: k) (b :: j) = ProObj v p a b

-- | Matrix multiplication over a list of middle objects, @⋁_b m(a,b) ⊗ n(b,c)@: the composite of two
-- enriched profunctors when the middle category is enumerable.
type MatMul :: forall {i} {j} {k}. forall (v :: Kind) -> [j] -> Type -> Type -> k -> i -> v
type family MatMul v bs m n a c where
  MatMul v '[] m n a c = InitialObject
  MatMul v (b ': bs) m n a c = (Entry v m a b ** Entry v n b c) || MatMul v bs m n a c

-- | The identity matrix on a bare set of objects, as the matrix of the tag 'Diagonal'. Over a
-- @v@-category the base matrix is its hom instead, @'Pro' ('Proarrow.Core.Hom' k)@.
type Delta :: forall {k}. forall (v :: Kind) -> k -> k -> v
type family Delta v a b where
  Delta v a a = Unit
  Delta v a b = InitialObject

data Diagonal

type instance Entry v Diagonal (a :: k) (b :: k) = Delta v a b

-- | Walks of at most @n@ steps along the graph @m@ over the base @i@: an arrow of the base, or one
-- edge followed by a walk of at most @n - 1@ steps. Each iteration is one matrix multiplication.
type Walks :: forall {k}. forall (v :: Kind) -> [k] -> Nat -> Type -> Type -> k -> k -> v
type family Walks v vs n i m a b where
  Walks v vs 'Z i m a b = Entry v i a b
  Walks v vs ('S n) i m a b = Entry v i a b || MatMul v vs m (WalksM v vs n i m) a b

-- | 'Walks' as a matrix, so that it can be multiplied again.
type WalksM :: forall {k}. Kind -> [k] -> Nat -> Type -> Type -> Type
data WalksM v vs n i m

type instance Entry v (WalksM v (vs :: [k]) n i m) (a :: k) (b :: k) = Walks v vs n i m a b

-- | The Kleene star of a @v@-weighted graph @m@ over the base @i@ on the objects @vs@: the free
-- @v@-category on the graph. The fixed point is reached after as many steps as there are objects,
-- since a shortest walk never revisits one. Its value-level counterpart for @BOOL@, with paths as
-- witnesses, is 'Proarrow.Category.Enriched.Thin.Composition.Reachable'.
type Closure v vs i m a b = Walks v vs (Length vs) i m a b

type Length :: [k] -> Nat
type family Length xs where
  Length '[] = 'Z
  Length (x ': xs) = 'S (Length xs)
