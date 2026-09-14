{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Cartesian monoidal categories ('Cartesian': tensor = product, with 'CopyDiscard' as
-- superclass by Fox's theorem) and cartesian closed ones ('CCC', 'BiCCC'). Lives above
-- "Proarrow.Category.Monoidal.CopyDiscard" rather than with the products, because the superclass
-- points that way.
module Proarrow.Category.Monoidal.Cartesian where

import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Colimit.BinaryCoproduct (HasCoproducts)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD (..), Prod (..), diag)
import Proarrow.Limit.Terminal (HasTerminalObject (..), Semicartesian)
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..))
import Proarrow.Profunctor.Representable (RepCostar (..), Representable (..), withObRep)

class (a ** b ~ a && b) => TensorIsProduct a b
instance (a ** b ~ a && b) => TensorIsProduct a b

-- | A cartesian monoidal category: the tensor is the product and the unit the terminal object.
-- By Fox's theorem this is exactly a 'CopyDiscard' category whose 'copy' and 'discard' are
-- natural, so 'CopyDiscard' is a superclass: every cartesian category supplies its diagonals as
-- comonoids, and anything asking only for copying and discarding (prisms, for instance) accepts
-- a cartesian category directly. The law relating the two is @copy = id &&& id@ and
-- @discard = terminate@.
class
  (HasProducts k, SymMonoidal k, Semicartesian k, CopyDiscard k, forall (a :: k) (b :: k). TensorIsProduct a b) =>
  Cartesian k

instance
  (HasProducts k, SymMonoidal k, Semicartesian k, CopyDiscard k, forall (a :: k) (b :: k). TensorIsProduct a b)
  => Cartesian k

-- | In a category with products every object is a comonoid via the diagonal and the terminal
-- map -- the natural comonoid structure that makes 'PROD' 'CopyDiscard' and 'Cartesian'.
instance (HasProducts k, Ob a) => Comonoid (PR (a :: k)) where
  counit = Prod terminate
  comult = Prod diag

instance (HasProducts k, Ob a) => CocommutativeComonoid (PR (a :: k))

-- | A category with products, viewed through 'PROD' as a monoidal category, is cartesian.
instance (HasProducts k) => CopyDiscard (PROD k)

-- | In a cartesian category the tensor /is/ the product ('TensorIsProduct'), but GHC only applies
-- that equation at the top of a type, never under another type family such as @('||')@, and
-- using the quantified form of it directly sends the solver in circles. These two identities take
-- the equation as an ordinary given -- discharged at the call site from the quantified superclass
-- of 'Cartesian' -- and let it be applied exactly where a product-typed leg meets tensor-typed
-- plumbing.
tensorToProduct :: forall {k} (a :: k) b. (HasBinaryProducts k, TensorIsProduct a b, Ob a, Ob b) => (a ** b) ~> (a && b)
tensorToProduct = withObProd @k @a @b id

productToTensor :: forall {k} (a :: k) b. (HasBinaryProducts k, TensorIsProduct a b, Ob a, Ob b) => (a && b) ~> (a ** b)
productToTensor = withObProd @k @a @b id

-- | Every functor between cartesian categories is oplax monoidal, @f (a && b) ~> f a && f b@ by the
-- projections and @f Unit ~> Unit@ by terminality. On the 'RepCostar' of its representable profunctor
-- this is 'Proarrow.Category.Monoidal.OplaxMonoidal'.
instance (Representable p, Cartesian j, Cartesian k) => MonoidalProfunctor (RepCostar (p :: j +-> k)) where
  one = withObRep @p @Unit (RepCostar terminate)
  RepCostar @a f ** RepCostar @b g = withOb2 @j @a @b (RepCostar (unparRepCartesian @p @a @b f g))

unparRepCartesian
  :: forall {j} {k} p (a :: j) b a' b'
   . ( Representable (p :: j +-> k)
     , Cartesian k
     , Cartesian j
     , TensorIsProduct a b
     , TensorIsProduct a' b'
     , Ob a
     , Ob b
     )
  => (p % a ~> a') -> (p % b ~> b') -> p % (a ** b) ~> (a' ** b')
unparRepCartesian f g = f . repMap @p (fst @j @a @b) &&& g . repMap @p (snd @j @a @b)

class (Cartesian k, Closed k) => CCC k
instance (Cartesian k, Closed k) => CCC k

class (CCC k, HasCoproducts k) => BiCCC k
instance (CCC k, HasCoproducts k) => BiCCC k

ap
  :: forall {j} {k} y a x p
   . (Closed j, Cartesian k, MonoidalProfunctor (p :: j +-> k), Ob y)
  => p a (x ~~> y)
  -> p a x
  -> p a y
ap pf px = dimap diag (apply @j @x @y) (pf ** px) \\ px
