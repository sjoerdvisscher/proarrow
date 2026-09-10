{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __setter__: the weakest write-side optic, applying a morphism to every focus ('SetterRes'
-- \/ 'overP'). It sits at the write-only top of the subtyping lattice alongside
-- 'Proarrow.Optic.Fold.Fold', so it has no builder of its own ('Proarrow.Optic.convert' a stronger
-- optic); its canonical eliminator is 'over' -- with 'set', '(%~)' and '(.~)' as shorthands -- via
-- the hom carrier 'Id'.
--
-- This module also hosts the tensor-action witness pair 'TensorW'\/'CoTensorW', shared by
-- "Proarrow.Optic.MonoidalTraversal" and "Proarrow.Optic.Tracer".
module Proarrow.Optic.Setter where

import Data.Kind (Type)
import Prelude (const)
import Prelude qualified as P

import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), type (**))
import Proarrow.Category.Monoidal.Closed (Closed (..), Exp)
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasCoproducts, right)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Functor (Prelude (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, Product, second)
import Proarrow.Optic (CompactFlavor, FLAVOR, Optic, Optic_ (..), Prostrong (..), SubFlavor (..))
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), RepCostar (..), Representable (..))

-- | A setter can only apply a pure function to the @a@'s it can see -- it can neither view nor
-- fold them. A traversal is both a setter and a fold.
type SetterRes :: forall {k}. FLAVOR k k
class (Profunctor p, Profunctor q) => SetterRes (p :: k +-> k) (q :: k +-> k) where
  overP :: p s a -> q b t -> (a ~> b) -> (s ~> t)

instance CompactFlavor SetterRes

-- | Every /representable/ residual is a setter: map the focus through the residual functor with
-- 'repMap'. This needs only 'Representable' @t@ -- no 'Proarrow.Category.Monoidal.Distributive.Traversable' -- which is exactly why
-- 'Proarrow.Optic.Setter.Setter' sits at the top of the lattice: functoriality of the residual is
-- all @over@ ever uses. Richer optics ('Proarrow.Optic.Lens.Lens', 'Proarrow.Optic.Traversal.Traversal', ...)
-- are this witness plus extra algebra on @t@.
instance (Representable t) => SetterRes (t :: k +-> k) (RepCostar t) where
  overP l (RepCostar r) f = r . repMap @t f . index l

instance (HasBinaryProducts k, Ob (s :: k)) => SetterRes (Rep (Product s)) (Corep (Product s)) where
  overP (Rep p) (Corep q) f = q . second @s f . p
instance (HasCoproducts k, Ob t) => SetterRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  overP (Rep p) (Corep q) f = q . right @t f . p
instance (CategoryOf k) => SetterRes (Id :: k +-> k) (Id :: k +-> k) where
  overP (Id l) (Id r) f = r . f . l
instance (SetterRes f g, SetterRes f' g') => SetterRes (f :.: f') (g' :.: g) where
  overP (f :.: f') (g' :.: g) = overP @f @g f g . overP @f' @g' f' g'

-- | Dually, every /corepresentable/ residual is a setter: map with 'corepMap'. Needs only
-- 'Corepresentable' @t@, not 'Proarrow.Category.Monoidal.Distributive.Cotraversable'.
instance (Corepresentable t) => SetterRes (CorepStar t) t where
  overP (CorepStar l) co f = coindex co . corepMap @t f . l

-- | The grate witness is a setter witness: map under the exponential. The 'Closed' structure
-- this needs rides in the instance context, not in @overP@'s own (weaker) constraint.
instance (Closed k, Ob (m :: k)) => SetterRes (Rep (Exp m) :: k +-> k) (Corep (Exp m)) where
  overP (Rep sm) (Corep mbt) f = mbt . (f ^^^ obj @m) . sm \\ f

-- | Witness pair for __tensor strength__: the focus @x@ sits inside @a '**' x@ with the residual
-- @a@ carried on the left. This is the tensor-action dual of the coproduct-action prism witness
-- @'Rep' ('Coproduct' t)@\/@'Corep' ('Coproduct' t)@ (whose 'monTravP' calls @'act' \@'CoprodAction'@):
-- here 'monTravP' calls @'act' \@'Tensor'@ -- exactly the strength any 'StrongDistributiveProfunctor'
-- already carries. Unlike the product-lens @'Rep' ('Product' a)@ that used to witness @'Strong'
-- 'Tensor'@ for the free traversal, this needs no @'Strong' 'ProdAction'@ and no @tensor = product@
-- ('Proarrow.Limit.BinaryProduct.Cartesian'): it is a genuine 'MonTravRes', so the free
-- monoidal-traversal profunctor @'ExOptic' 'MonTravRes'@ is 'Proarrow.Category.Monoidal.Strength.MonStrong'.
type TensorW :: forall {k}. k -> k +-> k
data TensorW a s x where
  TensorW :: (Ob a, Ob x) => (s ~> (a ** x)) -> TensorW a s x

-- | The covariant half of the 'TensorW' witness pair: rebuilds the target around the carried
-- residual, @(a '**' x) '~>' t@.
type CoTensorW :: forall {k}. k -> k +-> k
data CoTensorW a x t where
  CoTensorW :: (Ob a, Ob x) => ((a ** x) ~> t) -> CoTensorW a x t

instance (Monoidal k, Ob (a :: k)) => Profunctor (TensorW a :: k +-> k) where
  dimap l r (TensorW h) = TensorW ((obj @a ** r) . h . l) \\ r
  r \\ TensorW h = r \\ h
instance (Monoidal k, Ob (a :: k)) => Profunctor (CoTensorW a :: k +-> k) where
  dimap l r (CoTensorW i) = CoTensorW (r . i . (obj @a ** l)) \\ l
  r \\ CoTensorW i = r \\ i

instance (Monoidal k, Ob (a :: k)) => Proadjunction (TensorW a :: k +-> k) (CoTensorW a) where
  unit @c = withOb2 @k @a @c (CoTensorW id :.: TensorW id)
  counit (TensorW h :.: CoTensorW i) = i . h
instance (Monoidal k, Ob (a :: k)) => SetterRes (TensorW a :: k +-> k) (CoTensorW a) where
  overP (TensorW h) (CoTensorW i) f = i . (obj @a ** f) . h

type Setter (s :: k) (t :: k) a b = Optic (Prostrong SetterRes) s t a b
type Setter' s a = Setter s s a a

-- | Any flavor whose optics can set has strength for the hom carrier 'Id'.
instance (CategoryOf k, SubFlavor w SetterRes) => Prostrong (w :: FLAVOR k k) (Id :: k +-> k) where
  proact @f @g (f :.: Id h :.: g) = subFlavor @w @SetterRes @f @g (Id (overP @f @g f g h))

-- | Map over any optic that can act as a setter, in either encoding: a 'Prostrong'-flavored optic
-- needs @'SubFlavor' w 'SetterRes'@ (discharged by the bridge instance above), a
-- profunctor-class-flavored optic needs its class to hold for 'Id'.
over
  :: forall {k} c (s :: k) (t :: k) a b
   . (c (Id :: k +-> k))
  => Optic c s t a b -> (a ~> b) -> (s ~> t)
over (Optic l) f = unId (l (Id f))

-- | Apply a function through a concrete, @Type@-level 'Setter'.
infixl 8 %~

(%~) :: (c (Id :: Type +-> Type)) => Optic c s t a b -> (a -> b) -> (s -> t)
(%~) = over

-- | Replace the focus\/foci of a concrete, @Type@-level 'Setter' with a constant value.
infixl 8 .~

(.~) :: (c (Id :: Type +-> Type)) => Optic c s t a b -> b -> (s -> t)
l .~ b = l %~ const b

-- | Named version of '(.~)'.
set :: (c (Id :: Type +-> Type)) => Optic c s t a b -> b -> (s -> t)
set = (.~)

-- | Monadically replace the focus\/foci of a 'Setter' in the Kleisli category of @m@ with a
-- constant value, ignoring the old contents entirely.
mupdate
  :: forall m s t a b
   . (P.Monad m)
  => Setter (KL s :: KLEISLI (Star (Prelude m))) (KL t) (KL a) (KL b) -> b -> s -> m t
mupdate l b s = unPrelude (unStar (unKleisli (over l (Kleisli (Star (\_ -> Prelude (P.return b)))))) s)
