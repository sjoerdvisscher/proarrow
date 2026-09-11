{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}

-- | Optics for an arbitrary 'Proarrow.Category.Monoidal.Action.MonoidalAction': the 'ActFl' flavor,
-- whose witness pair is a matched pair of arrows into\/out of the action at some residual; its
-- specialisation to the tensor's self-action gives 'MonoidalOptic'. Also home to the __algebraic
-- lens__ ('AlgLensFl'), the tensor-action pair with an 'Algebra'-for-a-monad residual, and its
-- list-monad case, the __classifying lens__ ('ClassifyFl'), which is moreover an applicative optic.
module Proarrow.Optic.Action where

import Data.Kind (Type)
import Prelude (Monad (..), ($))
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal, Tensor, obj2, swap, type (**))
import Proarrow.Category.Monoidal.Action (Act, ActionAt, MonoidalAction (..), composeActs, decomposeActs)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Functor (Prelude (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (ExOptic, FLAVOR, Optic, Prostrong (..), SubFlavor (..), legs2prof, withLegs)
import Proarrow.Optic.AffineFold (AffineFoldFl)
import Proarrow.Optic.Fold (FoldFl)
import Proarrow.Optic.Getter (GetterFl)
import Proarrow.Optic.Kaleidoscope (CotravFl, KaleidoFl)
import Proarrow.Optic.MonoidalLens (MonLensFl)
import Proarrow.Optic.Setter (SetterFl)
import Proarrow.Optic.Traversal (MonTravFl, TravFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Costar (Costar, pattern Costar)
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
-- closure properties an optic flavor needs of its residuals.
class (Monad m) => Algebra m a where
  algebra :: m a -> a

instance (Monad m) => Algebra m (m a) where
  algebra = (>>= P.id)
instance (Monad m) => Algebra m () where
  algebra _ = ()
instance (Monad m, Algebra m a, Algebra m b) => Algebra m (a, b) where
  algebra mab = (algebra (P.fmap P.fst mab), algebra (P.fmap P.snd mab))

-- | The algebraic-lens flavor (Riley, /Categories of Optics/; Clarke et al.): the tensor-action
-- witness pair @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' x)@ of "Proarrow.Optic.MonoidalLens" --
-- legs @s -> (x, a)@ and @(x, b) -> t@ -- with the residual @x@ required to be an 'Algebra' for the
-- monad @m@. The algebra is what lets @put@ see a whole @m@-computation of sources rather than one:
-- 'classifyOf' collapses @m s@ to a single residual through it. Every algebraic lens is a
-- 'Proarrow.Optic.MonoidalLens.MonoidalLens' (the 'MonLensFl' superclass; in @Type@ every residual
-- is a comonoid), so it views, sets, folds and traverses as a lens does. 'Proarrow.Optic.Iso.IsoFl'
-- has no edge to it, since this flavor is @Type@-only and indexed by @m@.
type AlgLensFl :: (Type -> Type) -> FLAVOR Type Type
class (Monad m, MonLensFl p q) => AlgLensFl m (p :: Type +-> Type) (q :: Type +-> Type) where
  -- | Recover the two legs, with the residual @x@ existential and known to be an @m@-algebra.
  withAlgP :: p s a -> q b t -> (forall x. (Algebra m x) => (s -> (x, a)) -> ((x, b) -> t) -> r) -> r

instance (Algebra m x) => AlgLensFl m (Rep (ActionAt Tensor x)) (Corep (ActionAt Tensor x)) where
  withAlgP (Rep h) (Corep i) k = k @x h i
instance (Monad m) => AlgLensFl m Id Id where
  withAlgP (Id l) (Id r) k = k @() (\s -> ((), l s)) (\((), b) -> r b)
instance (AlgLensFl m f g, AlgLensFl m f' g') => AlgLensFl m (f :.: f') (g' :.: g) where
  withAlgP (f :.: f') (g' :.: g) k =
    withAlgP @m f g \ @xo ho io ->
      withAlgP @m f' g' \ @xi hi ii ->
        k @(xo, xi)
          (\s -> let (xo', a') = ho s; (xi', a) = hi a' in ((xo', xi'), a))
          (\((xo', xi'), b) -> io (xo', ii (xi', b)))

instance SubFlavor (AlgLensFl m) MonLensFl where subFlavor r = r
instance SubFlavor (AlgLensFl m) GetterFl where subFlavor r = r
instance SubFlavor (AlgLensFl m) MonTravFl where subFlavor r = r
instance SubFlavor (AlgLensFl m) TravFl where subFlavor r = r
instance SubFlavor (AlgLensFl m) SetterFl where subFlavor r = r
instance SubFlavor (AlgLensFl m) AffineFoldFl where subFlavor r = r
instance SubFlavor (AlgLensFl m) FoldFl where subFlavor r = r

-- | An algebraic lens: like a 'Proarrow.Optic.Lens.Lens', but @put@ is allowed to combine
-- information monadically -- @get :: s -> a@, @put :: m s -> b -> t@ -- rather than only ever
-- seeing the /last/ @s@.
type AlgebraicLens m (s :: Type) (t :: Type) a b = Optic (Prostrong (AlgLensFl m)) s t a b

-- | Build an algebraic lens from @get@ and a monadic @put@; the residual is @m s@ itself.
mkAlgebraicLens
  :: forall m s t a b
   . (Monad m) => (s -> a) -> (m s -> b -> t) -> AlgebraicLens m s t a b
mkAlgebraicLens v u =
  legs2prof @(AlgLensFl m)
    (Rep @a @(ActionAt Tensor (m s)) (\s -> (return s, v s)))
    (Corep @b @(ActionAt Tensor (m s)) (P.uncurry u))

-- | Classify a monadic computation of @s@'s through an 'AlgebraicLens' (or any stronger optic,
-- in any encoding), given a replacement focus @b@ -- generalizing "set" to combine every @s@ the
-- computation might produce (via its residual's 'Algebra') rather than only ever seeing the last one.
classifyOf
  :: forall m c s t a b
   . (Monad m, c (ExOptic (AlgLensFl m) a b))
  => Optic c s t a b -> m s -> b -> t
classifyOf optic ms b =
  withLegs @(AlgLensFl m) optic \l r -> withAlgP @m l r \f g -> g (algebra (P.fmap (P.fst . f) ms), b)

infixl 8 .?
(.?) :: forall m c s t a b. (Monad m, c (ExOptic (AlgLensFl m) a b)) => Optic c s t a b -> b -> m s -> t
(.?) l b ms = classifyOf @m l ms b

-- | The __classifying lens__ (Clarke et al., Example 3.11): the algebraic lens for the list monad.
-- Its residual is a list algebra, i.e. a monoid, and tensoring with a monoid is an applicative
-- functor (the writer applicative) -- so a classifying lens is also a kaleidoscope
-- ('Proarrow.Optic.Kaleidoscope.KaleidoFl'), the meet of the two flavors. This is what lets it compose
-- with a kaleidoscope to a kaleidoscope again (Clarke et al., Remark 3.28): a lens composed
-- with a kaleidoscope is not a kaleidoscope, since a product functor is not applicative, but a
-- product /by a monoid/ is. The two structures on the residual are assumed to agree, as they do
-- for the list @m s@ itself ('P.++' and @join@) that 'classifyingLens' uses.
type ClassifyFl :: FLAVOR Type Type
class (AlgLensFl [] p q, KaleidoFl p q) => ClassifyFl (p :: Type +-> Type) (q :: Type +-> Type)

instance (Algebra [] x, P.Monoid x) => ClassifyFl (Rep (ActionAt Tensor x)) (Corep (ActionAt Tensor x))
instance ClassifyFl Id Id
instance (ClassifyFl f g, ClassifyFl f' g') => ClassifyFl (f :.: f') (g' :.: g)

instance SubFlavor ClassifyFl (AlgLensFl []) where subFlavor r = r
instance SubFlavor ClassifyFl KaleidoFl where subFlavor r = r
instance SubFlavor ClassifyFl CotravFl where subFlavor r = r
instance SubFlavor ClassifyFl MonLensFl where subFlavor r = r
instance SubFlavor ClassifyFl GetterFl where subFlavor r = r
instance SubFlavor ClassifyFl MonTravFl where subFlavor r = r
instance SubFlavor ClassifyFl TravFl where subFlavor r = r
instance SubFlavor ClassifyFl SetterFl where subFlavor r = r
instance SubFlavor ClassifyFl AffineFoldFl where subFlavor r = r
instance SubFlavor ClassifyFl FoldFl where subFlavor r = r

type ClassifyingLens (s :: Type) (t :: Type) a b = Optic (Prostrong ClassifyFl) s t a b

-- | Build a classifying lens from @get@ and a @classify :: [s] -> b -> t@; the residual is @[s]@.
classifyingLens :: forall s t a b. (s -> a) -> ([s] -> b -> t) -> ClassifyingLens s t a b
classifyingLens v u =
  legs2prof @ClassifyFl
    (Rep @a @(ActionAt Tensor [s]) (\s -> ([s], v s)))
    (Corep @b @(ActionAt Tensor [s]) (P.uncurry u))

-- | The carrier of the literature's algebraic-lens eliminator: @'Costar' m@, i.e. @m a -> b@.
-- Absorbing an algebraic-lens witness pair collapses the residuals of the incoming computation
-- through their algebra and hands the foci on as one @m@-computation. Together with the
-- 'Proarrow.Optic.PowerGrate.PowerGrateFl' instance for the same carrier, this is what lets an
-- algebraic lens composed with a kaleidoscope classify an /aggregate/: run the composite at
-- @'Costar' (\`Prelude\` m)@.
instance (Monad m) => Prostrong (AlgLensFl m) (Costar (Prelude m)) where
  proact (f :.: Costar g :.: g') =
    withAlgP @m f g' \l r -> Costar (\(Prelude ms) -> r (algebra (P.fmap (P.fst . l) ms), g (Prelude (P.fmap (P.snd . l) ms))))
