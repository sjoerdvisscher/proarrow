{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}

-- | Lenses for an arbitrary 'Monoidal' tensor rather than a 'Proarrow.Limit.BinaryProduct.Cartesian' product: the residual
-- @m@ is consumed\/produced via '**' instead of being duplicated\/discarded via the diagonal, so
-- unlike "Proarrow.Optic.Lens" this needs no 'Proarrow.Limit.BinaryProduct.Cartesian' instance,
-- only 'Monoidal'. It's the 'ActFl' flavor specialized to the tensor's own self-action,
-- 'Tensor'.
module Proarrow.Optic.Action where

import Data.Kind (Type)
import Prelude (Monad (..), ($))
import Prelude qualified as P

import Proarrow.Category.Instance.Sub (SUBCAT (..))
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal, Tensor, obj2, swap, type (**))
import Proarrow.Category.Monoidal.Action (Act, ActionAt, MonoidalAction (..), SubAction, composeActs, decomposeActs)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (FLAVOR, Optic, Prostrong (..), legs2prof, withLegs)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | Any 'MonoidalAction' gives rise to a flavor: the witness pair is a matched pair of arrows
-- into\/out of the action for some shared, existentially hidden index @x@. 'Proarrow.Optic.Lens.LensFl'\/'Proarrow.Optic.Prism.PrismFl'
-- are (unspelled-out) special cases of this for 'Proarrow.Category.Monoidal.Action.ProdAction'\/'Proarrow.Category.Monoidal.Action.CoprodAction'.
type ActFl :: forall {m} {k}. (m, k) +-> k -> FLAVOR k k
class (MonoidalAction act, Profunctor p, Profunctor q) => ActFl act (p :: k +-> k) (q :: k +-> k) where
  withActP :: p s a -> q b t -> (forall x. (Ob x) => (s ~> Act act x a) -> (Act act x b ~> t) -> r) -> r

instance (MonoidalAction act, Ob x) => ActFl act (Rep (ActionAt act x)) (Corep (ActionAt act x)) where
  withActP (Rep f) (Corep g) k = k @x f g
instance (MonoidalAction act) => ActFl act (Id :: k +-> k) (Id :: k +-> k) where
  withActP (Id f) (Id g) k = k @Unit (unitorInv @act . f) (g . unitor @act) \\ f \\ g
instance (ActFl act f g, ActFl act f' g') => ActFl act (f :.: f') (g' :.: g) where
  withActP @_ @a @b (f :.: f'@Objs) (g'@Objs :.: g) k =
    withActP @act @f @g f g \ @x f1 g1 ->
      withActP @act @f' @g' f' g' \ @y f2 g2 ->
        withOb2 @_ @x @y $
          k @(x ** y) (composeActs @act @x @y @a f1 f2) (decomposeActs @act @x @y @b g2 g1)

type MonoidalOptic (s :: k) (t :: k) a b = Optic (Prostrong (ActFl Tensor)) s t a b

mkMonoidal
  :: forall {k} (m :: k) (a :: k) (b :: k) s t
   . (Monoidal k, Ob m, Ob a, Ob b) => (s ~> m ** a) -> (m ** b ~> t) -> MonoidalOptic s t a b
mkMonoidal sma mbt = legs2prof @(ActFl Tensor) (Rep @a @(ActionAt Tensor m) sma) (Corep @b @(ActionAt Tensor m) mbt)

_1 :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => MonoidalOptic (a ** c) (b ** c) a b
_1 = mkMonoidal @c (swap @k @a @c) (swap @k @c @b)

_2 :: forall {k} (a :: k) b c. (SymMonoidal k, Ob a, Ob b, Ob c) => MonoidalOptic (c ** a) (c ** b) a b
_2 = mkMonoidal @c (obj2 @c @a) (obj2 @c @b)

-- | An Eilenberg-Moore algebra for the (Haskell) monad @m@: a way to collapse an @m@-computation
-- of @a@'s down to a single @a@, coherently with 'Monad'\'s own unit\/multiplication. Products of
-- algebras are algebras, and @m a@ is always an algebra for itself (via @join@) -- exactly the
-- closure properties 'SubAction' needs to restrict 'Tensor' to the objects that have one.
class (Monad m) => Algebra m a where
  algebra :: m a -> a

instance (Monad m) => Algebra m (m a) where
  algebra = (>>= P.id)
instance (Monad m) => Algebra m () where
  algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where
  algebra mab = (algebra (P.fmap P.fst mab), algebra (P.fmap P.snd mab))

-- | An algebraic lens (Riley, /Categories of Optics/): like a 'Proarrow.Optic.Lens.Lens', but
-- @put@ is allowed to combine information monadically -- @get :: s -> a@, @put :: m s -> b -> t@
-- -- rather than only ever seeing the /last/ @s@. The residual is restricted to 'Algebra' @m@
-- objects, so the atomic constructor below can always pick @m s@ itself as the residual.
type AlgAction m = SubAction (Algebra m) Tensor

type AlgebraicLens m (s :: Type) (t :: Type) a b = Optic (Prostrong (ActFl (AlgAction m))) s t a b

mkAlgebraicLens
  :: forall m s t a b
   . (Monad m) => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u =
  legs2prof @(ActFl (AlgAction m))
    (Rep @a @(ActionAt (AlgAction m) (SUB (m s))) (\s -> (return s, v s)))
    (Corep @b @(ActionAt (AlgAction m) (SUB (m s))) (P.uncurry u))

-- | Classify a monadic computation of @s@'s through an 'AlgebraicLens', given a replacement
-- focus @b@ -- generalizing "set" to combine every @s@ the computation might produce (via its
-- residual's 'Algebra') rather than only ever seeing the last one.
classifyOf :: forall m s t a b. (Monad m) => AlgebraicLens m s t a b -> m s -> b -> t
classifyOf optic =
  withLegs @(ActFl (AlgAction m)) optic \l r -> withActP @(AlgAction m) l r \f g ms b -> g (algebra (P.fmap (P.fst . f) ms), b)

infixl 8 .?
(.?) :: (Monad m) => AlgebraicLens m s t a b -> b -> m s -> t
(.?) l b ms = classifyOf l ms b
