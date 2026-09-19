{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Optics for an arbitrary 'Proarrow.Category.Monoidal.Action.MonoidalAction': the 'ActFl' flavor,
-- whose witness pair is a matched pair of arrows into\/out of the action at some residual; its
-- specialisation to the tensor's self-action gives 'MonoidalOptic'. Also home to the __algebraic
-- lens__ ('AlgLensFl'), the tensor-action pair with an 'Algebra'-for-a-monad residual, and its
-- list-monad case, the __classifying lens__ ('ClassifyFl'), which is moreover a kaleidoscope.
module Proarrow.Optic.Action where

import Data.Kind (Constraint)
import Prelude (($))
import Prelude qualified as P

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , OplaxMonoidalRep
  , SymMonoidal
  , Tensor
  , unpar0Rep
  , unparRep
  , type (**)
  )
import Proarrow.Category.Monoidal.Action (Act, ActionAt, MonoidalAction (..), composeActs, decomposeActs)
import Proarrow.Colimit.BinaryCoproduct (HasCoproducts)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Functor (Functor)
import Proarrow.Monoid (Comonoid, Monoid)
import Proarrow.Monoid qualified as Mon
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (ExOptic, FLAVOR, Optic, Prostrong (..), legs2prof, withLegs)
import Proarrow.Optic.Kaleidoscope (KaleidoFl)
import Proarrow.Optic.MonoidalLens (MonLensFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star)
import Proarrow.Profunctor.Representable (Rep (..), RepCostar (..), Representable (..))
import Proarrow.Promonad (Monad, bind, return)

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

-- | An Eilenberg-Moore algebra for the monad @m@ -- a representable 'Promonad' on @k@, acting as
-- the functor @m '%' -@ ("Proarrow.Promonad"): a structure map @m % a ~> a@, coherent with the
-- monad's unit and multiplication. The free algebras @m % s@ are the ones an algebraic lens is
-- built from ('algebraicLens').
--
-- There are deliberately no instances for the unit or for products of algebras, and there cannot be:
-- @Unit@ and @('**')@ are type families, which may not head an instance. That is why 'withAlgP'
-- passes the structure map as a /value/ -- the composition instance pairs two algebras with
-- 'unparRep' and the identity witness supplies the unit one with 'unpar0Rep', neither needing an
-- 'Algebra' instance. A witness pair whose residual is the unit is the identity optic up to the
-- unitors, so nothing is lost.
type Algebra :: forall {k}. (k +-> k) -> k -> Constraint
class (Monad m, Ob a) => Algebra (m :: k +-> k) (a :: k) where
  algebra :: m % a ~> a

-- | The free algebras of a monad @m@, wrapped as the representable promonad @'Star' m@.
instance (Monad (Star m), Ob (m a), Ob a) => Algebra (Star m) (m a) where
  algebra = bind @(Star m) id

-- | The algebraic-lens flavor (Riley, /Categories of Optics/; Clarke et al.): the tensor-action
-- witness pair @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' x)@ of "Proarrow.Optic.MonoidalLens" --
-- legs @s ~> x ** a@ and @x ** b ~> t@ -- with the residual @x@ an 'Algebra' for @m@. The flavor
-- itself asks only that the functor @m '%'@ be oplax monoidal, enough to pair and discard residuals;
-- the monad structure arrives with each 'Algebra' witness, not with the flavor.
-- The algebra is what lets @put@ see a whole @m@-computation of sources rather than one:
-- 'classifyOf' collapses @m % s@ to a single residual through it. Every algebraic lens is a
-- 'Proarrow.Optic.MonoidalLens.MonoidalLens' (the 'MonLensFl' superclass: the residual is a
-- comonoid), so it views, sets, folds and traverses as a lens does. 'withAlgP' hands the algebra
-- over as a value, so composites pair algebras without an instance for the product.
type AlgLensFl :: forall {k}. (k +-> k) -> FLAVOR k k
class (OplaxMonoidalRep m, MonLensFl p q) => AlgLensFl (m :: k +-> k) (p :: k +-> k) (q :: k +-> k) where
  -- | Recover the two legs and the algebra of the (existential) residual @x@.
  withAlgP
    :: p s a -> q b t -> (forall (x :: k). (Ob x) => (m % x ~> x) -> (s ~> x ** a) -> (x ** b ~> t) -> r) -> r

instance
  (OplaxMonoidalRep m, Algebra m x, Comonoid (x :: k))
  => AlgLensFl m (Rep (ActionAt Tensor x) :: k +-> k) (Corep (ActionAt Tensor x))
  where
  withAlgP (Rep h) (Corep i) k = k @x (algebra @m @x) h i
instance (OplaxMonoidalRep (m :: k +-> k)) => AlgLensFl m (Id :: k +-> k) (Id :: k +-> k) where
  withAlgP (Id l) (Id r) k = k @Unit (unpar0Rep @m) (leftUnitorInv . l) (r . leftUnitor) \\ l \\ r
instance
  forall k (m :: k +-> k) (f :: k +-> k) (f' :: k +-> k) (g :: k +-> k) (g' :: k +-> k)
   . (AlgLensFl m f g, AlgLensFl m f' g')
  => AlgLensFl m (f :.: f') (g' :.: g)
  where
  withAlgP @_ @afoc @bfoc (f :.: f'@Objs) (g'@Objs :.: g) kk =
    withAlgP @m f g \ @(xo :: k) algo ho io ->
      withAlgP @m f' g' \ @(xi :: k) algi hi ii ->
        withOb2 @k @xo @xi
          ( kk @(xo ** xi)
              ((algo ** algi) . unparRep @m @xo @xi)
              (associatorInv @k @xo @xi @afoc . (obj @xo ** hi) . ho)
              (io . (obj @xo ** ii) . associator @k @xo @xi @bfoc)
          )

-- | An algebraic lens: like a 'Proarrow.Optic.Lens.Lens', but @put@ is allowed to combine
-- information monadically -- @get :: s ~> a@, @put :: m % s ** b ~> t@ -- rather than only ever
-- seeing the /last/ @s@.
type AlgebraicLens m (s :: k) (t :: k) a b = Optic (Prostrong (AlgLensFl m)) s t a b

-- | Build an algebraic lens from @get@ and a monadic @put@; the residual is the free algebra
-- @m % s@ itself (which must be a comonoid, as must @s@ to be kept alongside its focus).
algebraicLens
  :: forall {k} m (s :: k) (t :: k) a b
   . (Algebra m (m % s), Comonoid (m % s), Comonoid s, OplaxMonoidalRep m, Ob a, Ob b)
  => (s ~> a) -> (m % s ** b ~> t) -> AlgebraicLens m s t a b
algebraicLens v u =
  legs2prof @(AlgLensFl m)
    (Rep @a @(ActionAt Tensor (m % s)) ((return @m @s ** v) . Mon.comult @s))
    (Corep @b @(ActionAt Tensor (m % s)) u)

-- | Classify a monadic computation of @s@'s through an 'AlgebraicLens' (or any stronger optic,
-- in any encoding), given a replacement focus @b@ -- generalizing "set" to combine every @s@ the
-- computation might produce (via its residual's 'Algebra') rather than only ever seeing the last one.
-- The focus @a@ is discarded under the monad, hence must be a comonoid.
classifyOf
  :: forall {k} m c (s :: k) (t :: k) a b
   . (OplaxMonoidalRep m, Comonoid a, (Ob a, Ob b) => c (ExOptic (AlgLensFl m) a b))
  => Optic c s t a b -> (m % s ** b) ~> t
classifyOf optic =
  withLegs @(AlgLensFl m) optic \l r ->
    withAlgP @m l r \ @x alg h i ->
      (i . ((alg . repMap @m (rightUnitor @k @x . (obj @x ** Mon.counit @a) . h)) ** obj @b)) \\ r

infixl 8 .?

-- | 'classifyOf' for a Haskell monad, curried: @optic .? b $ fs@.
(.?)
  :: forall f c s t a b
   . (P.Monad f, Functor f, c (ExOptic (AlgLensFl (Star f)) a b))
  => Optic c s t a b -> b -> f s -> t
(.?) l b fs = classifyOf @(Star f) l (fs, b)

-- | The __classifying lens__ (Clarke et al., Example 3.11): the algebraic lens for the list monad,
-- here for any monad @l@ whose algebras are monoids. Tensoring with a monoid is an applicative
-- functor (the writer applicative) -- so a classifying lens is also a kaleidoscope
-- ('Proarrow.Optic.Kaleidoscope.KaleidoFl'), the meet of the two flavors. This is what lets it compose
-- with a kaleidoscope to a kaleidoscope again (Clarke et al., Remark 3.28): a lens composed
-- with a kaleidoscope is not a kaleidoscope, since a product functor is not applicative, but a
-- product /by a monoid/ is. The algebra and the monoid on the residual are assumed to agree, as
-- they do for the free algebra @l % s@ of the list monad (@join@ and @++@) that 'classifyingLens' uses.
type ClassifyFl :: forall {k}. (k +-> k) -> FLAVOR k k
class (AlgLensFl l p q, KaleidoFl p q) => ClassifyFl (l :: k +-> k) (p :: k +-> k) (q :: k +-> k)

instance
  (OplaxMonoidalRep l, Algebra l x, Monoid x, Comonoid x, SymMonoidal k, HasCoproducts k)
  => ClassifyFl l (Rep (ActionAt Tensor x) :: k +-> k) (Corep (ActionAt Tensor x))
instance (OplaxMonoidalRep (l :: k +-> k)) => ClassifyFl l (Id :: k +-> k) (Id :: k +-> k)
instance (ClassifyFl l f g, ClassifyFl l f' g') => ClassifyFl l (f :.: f') (g' :.: g)

type ClassifyingLens l (s :: k) (t :: k) a b = Optic (Prostrong (ClassifyFl l)) s t a b

-- | Build a classifying lens from @get@ and a @classify :: l % s ** b ~> t@; the residual is the
-- free algebra @l % s@, e.g. the list of sources.
classifyingLens
  :: forall {k} l (s :: k) (t :: k) a b
   . ( Algebra l (l % s)
     , Monoid (l % s)
     , Comonoid (l % s)
     , Comonoid s
     , OplaxMonoidalRep l
     , SymMonoidal k
     , HasCoproducts k
     , Ob a
     , Ob b
     )
  => (s ~> a) -> (l % s ** b ~> t) -> ClassifyingLens l s t a b
classifyingLens v u =
  legs2prof @(ClassifyFl l)
    (Rep @a @(ActionAt Tensor (l % s)) ((return @l @s ** v) . Mon.comult @s))
    (Corep @b @(ActionAt Tensor (l % s)) u)

-- | The carrier of the literature's algebraic-lens eliminator: @'RepCostar' m@, i.e. @m % a ~> b@.
-- Absorbing an algebraic-lens witness pair collapses the residuals of the incoming computation
-- through their algebra and hands the foci on as one @m@-computation.
instance (OplaxMonoidalRep (m :: k +-> k)) => Prostrong (AlgLensFl m) (RepCostar m :: k +-> k) where
  proact (f :.: RepCostar @afoc g :.: g') =
    withAlgP @m f g' \ @x alg h i ->
      RepCostar (i . (alg ** g) . unparRep @m @x @afoc . repMap @m h) \\ g \\ f
