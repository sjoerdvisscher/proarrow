{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __setter__: the weakest write-side optic, applying a morphism to every focus ('SetterFl'
-- \/ 'overP'). It sits at the write-only top of the subtyping lattice alongside
-- 'Proarrow.Optic.Fold.Fold', so it has no builder of its own ('Proarrow.Optic.convert' a stronger
-- optic); its canonical eliminator is 'over' -- with 'set', '(%~)' and '(.~)' as shorthands -- via
-- the generic 'ExOptic' carrier.
--
-- This module also hosts the 'SetterFl' instance of the tensor-action witness pair
-- @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' a)@, shared by "Proarrow.Optic.MonoidalTraversal" and
-- "Proarrow.Optic.Tracer".
module Proarrow.Optic.Setter where

import Data.Kind (Type)
import Prelude (const)
import Prelude qualified as P

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..), Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Category.Monoidal.Closed (Closed (..), Exp)
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasCoproducts, right)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Functor (Prelude (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, Product, second)
import Proarrow.Optic (ExOptic, FLAVOR, Optic, Prostrong (..), withLegs)
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), RepCostar (..), Representable (..))

-- | A setter can only apply a pure function to the @a@'s it can see -- it can neither view nor
-- fold them. A traversal is both a setter and a fold.
type SetterFl :: forall {k}. FLAVOR k k
class (Profunctor p, Profunctor q) => SetterFl (p :: k +-> k) (q :: k +-> k) where
  overP :: p s a -> q b t -> (a ~> b) -> (s ~> t)

-- | Every /representable/ residual is a setter: map the focus through the residual functor with
-- 'repMap'. This needs only 'Representable' @t@ -- no 'Proarrow.Category.Monoidal.Distributive.Traversable' -- which is exactly why
-- 'Proarrow.Optic.Setter.Setter' sits at the top of the lattice: functoriality of the residual is
-- all @over@ ever uses. Richer optics ('Proarrow.Optic.Lens.Lens', 'Proarrow.Optic.Traversal.Traversal', ...)
-- are this witness plus extra algebra on @t@.
instance (Representable t) => SetterFl (t :: k +-> k) (RepCostar t) where
  overP l (RepCostar r) f = r . repMap @t f . index l

instance (HasBinaryProducts k, Ob (s :: k)) => SetterFl (Rep (Product s)) (Corep (Product s)) where
  overP (Rep p) (Corep q) f = q . second @s f . p
instance (HasCoproducts k, Ob t) => SetterFl (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  overP (Rep p) (Corep q) f = q . right @t f . p
instance (CategoryOf k) => SetterFl (Id :: k +-> k) (Id :: k +-> k) where
  overP (Id l) (Id r) f = r . f . l
instance (SetterFl f g, SetterFl f' g') => SetterFl (f :.: f') (g' :.: g) where
  overP (f :.: f') (g' :.: g) = overP @f @g f g . overP @f' @g' f' g'

-- | Dually, every /corepresentable/ residual is a setter: map with 'corepMap'. Needs only
-- 'Corepresentable' @t@, not 'Proarrow.Category.Monoidal.Distributive.Cotraversable'.
instance (Corepresentable t) => SetterFl (CorepStar t) t where
  overP (CorepStar l) co f = coindex co . corepMap @t f . l

-- | The grate witness is a setter witness: map under the exponential. The 'Closed' structure
-- this needs rides in the instance context, not in @overP@'s own (weaker) constraint.
instance (Closed k, Ob (m :: k)) => SetterFl (Rep (Exp m) :: k +-> k) (Corep (Exp m)) where
  overP (Rep sm) (Corep mbt) f = mbt . (f ^^^ obj @m) . sm \\ f

-- | The tensor-action witness pair @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' a)@: the focus @x@
-- sits inside @a ** x@ with the residual @a@ carried on the left (legs @s ~> a ** x@ and
-- @a ** x ~> t@). It is a setter witness by mapping under the tensor, and the tensor-strength
-- generator for the free traversal profunctor (see "Proarrow.Optic.MonoidalTraversal"); read the
-- other way round it is the tracer witness (see "Proarrow.Optic.Tracer").
instance (Monoidal k, Ob (a :: k)) => SetterFl (Rep (ActionAt Tensor a) :: k +-> k) (Corep (ActionAt Tensor a)) where
  overP (Rep h) (Corep i) f = i . (obj @a ** f) . h

type Setter (s :: k) (t :: k) a b = Optic (Prostrong SetterFl) s t a b
type Setter' s a = Setter s s a a

-- | Map over any optic that can act as a setter, in either encoding: run it at its witness pair
-- ('ExOptic' 'SetterFl', via 'withLegs') and apply 'overP'.
over
  :: forall {k} c (s :: k) (t :: k) a b
   . (CategoryOf k, (Ob a, Ob b) => c (ExOptic SetterFl a b))
  => Optic c s t a b -> (a ~> b) -> (s ~> t)
over o f = withLegs @SetterFl o \ @p @q p q -> overP @p @q p q f

-- | Apply a function through a concrete, @Type@-level 'Setter'.
infixl 8 %~

(%~) :: (c (ExOptic SetterFl a b)) => Optic c (s :: Type) t a b -> (a -> b) -> (s -> t)
(%~) = over

-- | Replace the focus\/foci of a concrete, @Type@-level 'Setter' with a constant value.
infixl 8 .~

(.~) :: (c (ExOptic SetterFl a b)) => Optic c (s :: Type) t a b -> b -> (s -> t)
l .~ b = l %~ const b

-- | Named version of '(.~)'.
set :: (c (ExOptic SetterFl a b)) => Optic c (s :: Type) t a b -> b -> (s -> t)
set = (.~)

-- | Monadically replace the focus\/foci of a 'Setter' in the Kleisli category of @m@ with a
-- constant value, ignoring the old contents entirely.
mupdate
  :: forall m s t a b
   . (P.Monad m)
  => Setter (KL s :: KLEISLI (Star (Prelude m))) (KL t) (KL a) (KL b) -> b -> s -> m t
mupdate l b s = unPrelude (unStar (unKleisli (over l (Kleisli (Star (\_ -> Prelude (P.return b)))))) s)
