{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __cotraversal__ and the __kaleidoscope__: two flavors with the same witnesses -- the
-- representable 'StrongDistributiveProfunctor's, i.e. applicative functors rendered as profunctors,
-- with their 'RepCostar's -- that differ in what they can be eliminated through.
--
-- Both are the mirror image of 'Proarrow.Optic.Traversal.MonTravFl'. All three rest on the same
-- square @t :.: p ~> p :.: t@ between a functor @t@ and a 'StrongDistributiveProfunctor' @p@ -- in
-- @Type@, @sequenceA :: t (f a) -> f (t a)@. A monoidal traversal fixes the traversable @t@ as the
-- witness and quantifies over the applicative carrier @p@; the optics here fix the applicative @p@
-- as the witness and quantify over the carriers it passes through:
--
-- * A 'Cotraversal' passes through every 'Cotraversable' carrier -- the class whose law is that
--   square with @p@ /arbitrary/. That is the literal mirror of a traversal, and it holds for
--   finite shapes ('Proarrow.Category.Monoidal.Distributive.Cotraversable' @('RepCostar' t)@ for a
--   traversable representable @t@, 'Id', products, sums).
--
-- * A 'Kaleidoscope' passes through every 'Kaleidoscopic' carrier -- the same square, but only for
--   /representable/ @p@, which is exactly the kaleidoscope of Clarke et al. (/Profunctor optics: a
--   categorical update/): the optic for the action of applicative functors,
--   @∫^{F applicative} C(S, F A) × C(F B, T)@, eliminated by @Traversable@ carriers through
--   @sequenceA@. In @Type@ this admits the unbounded shapes: @'Costar' ('Prelude' t)@ for a
--   @Traversable t@, the @Aggregating@ module of the literature. Those are not 'Cotraversable': a
--   list can only pass a strong distributive profunctor through by /knowing it is an applicative/
--   -- a generic structural recursion diverges on strict witnesses such as 'Rep'.
--
-- Every 'Cotraversable' carrier is 'Kaleidoscopic' ('cotravAct'), so @'KaleidoFl' <: 'CotravFl'@: the
-- applicative optic is the stronger flavor. Both sit below 'Proarrow.Optic.Setter.SetterFl' only --
-- one can @over@ through an applicative, but not fold out of one. 'Proarrow.Optic.PowerGrate.PowerGrateFl'
-- (tensor powers, the reader applicative) is a subflavor of 'KaleidoFl', and so is the tensor-action pair
-- for a /monoid/ residual (the writer applicative) -- which is how an algebraic lens for the list
-- monad composes with a kaleidoscope to a kaleidoscope again ('Proarrow.Optic.Action.ClassifyFl').
module Proarrow.Optic.Kaleidoscope
  ( -- * The cotraversal
    CotravFl (..)
  , Cotraversal
  , Cotraversal'
  , cotraversal
  , cotraverseOf

    -- * The kaleidoscope
  , KaleidoFl (..)
  , Kaleidoscope
  , Kaleidoscope'
  , kaleidoscope
  , kaleidoscopeOf

    -- * Carriers
  , Kaleidoscopic (..)
  , cotravAct
  , CotravAs (..)
  , WrapRep (..)
  ) where

import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category.Monoidal (MonoidalProfunctor (..), SymMonoidal, Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Category.Monoidal.Closed (Closed, Exp)
import Proarrow.Category.Monoidal.Distributive (Cotraversable (..), StrongDistributiveProfunctor, Traversable)
import Proarrow.Colimit.BinaryCoproduct (HasCoproducts)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (//), (\\), type (+->))
import Proarrow.Functor (Prelude (..))
import Proarrow.Monoid (Comonoid, Monoid)
import Proarrow.Optic (ExOptic, FLAVOR, Optic, Prostrong (..), SubFlavor (..), legs2prof, withLegs)
import Proarrow.Optic.Setter (SetterFl (..))
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..), RepCostar (..), Representable (..), repUniv)

-- * Carriers

-- | The carriers of the kaleidoscope: profunctors that every representable
-- 'StrongDistributiveProfunctor' @p@ -- i.e. every applicative functor @p % -@ -- acts on by
-- application. Where a traversal's carriers are the applicatives themselves, a kaleidoscope's
-- carriers are the things applicatives can be sequenced through: every 'Cotraversable' profunctor
-- ('cotravAct'), and in @Type@ also @'Costar' ('Prelude' t)@ for any @Traversable t@.
type Kaleidoscopic :: forall {k}. (k +-> k) -> Constraint
class (Profunctor r) => Kaleidoscopic (r :: k +-> k) where
  kaleidoAct :: forall p a b. (Representable p, StrongDistributiveProfunctor (p :: k +-> k)) => r a b -> r (p % a) (p % b)

-- | 'kaleidoAct' for any 'Cotraversable' carrier: let the witness through.
cotravAct
  :: forall {k} p r (a :: k) b
   . (Cotraversable r, Representable p, StrongDistributiveProfunctor p)
  => r a b -> r (p % a) (p % b)
cotravAct rab = rab // case cotraverse (repUniv @p @a :.: rab) of x :.: y -> rmap (index y) x

-- | A 'Cotraversable' carrier, tagged as the 'Kaleidoscopic' carrier it also is. This is what makes
-- every kaleidoscope witness a cotraversal witness (the default 'cotravP').
newtype CotravAs r a b = CotravAs {unCotravAs :: r a b}

instance (Profunctor r) => Profunctor (CotravAs r) where
  dimap l r (CotravAs p) = CotravAs (dimap l r p)
  r \\ CotravAs p = r \\ p
instance (Cotraversable r) => Kaleidoscopic (CotravAs r) where
  kaleidoAct @p (CotravAs r) = CotravAs (cotravAct @p r)

-- | The general carrier: the 'RepCostar' of a traversable representable functor.
instance (Traversable t, Representable t) => Kaleidoscopic (RepCostar t) where
  kaleidoAct @p = cotravAct @p

-- | The applicative functor a representable 'StrongDistributiveProfunctor' on 'Type' represents:
-- @pure@ is 'one' and @liftA2@ is '**'.
newtype WrapRep p x = WrapRep {unwrapRep :: p % x}

instance (Representable (p :: Type +-> Type)) => P.Functor (WrapRep p) where
  fmap f (WrapRep x) = WrapRep (repMap @p f x)
instance (Representable p, StrongDistributiveProfunctor (p :: Type +-> Type)) => P.Applicative (WrapRep p) where
  pure x = WrapRep (index (rmap (\() -> x) (one @p)) ())
  liftA2 f (WrapRep x) (WrapRep y) = WrapRep (index (rmap (P.uncurry f) (repUniv @p ** repUniv @p)) (x, y))

-- | @'Costar' ('Prelude' t)@ for a traversable @t@: sequence the applicative through @t@, then
-- aggregate. This carrier is /not/ 'Cotraversable', see the module header.
instance (P.Traversable t) => Kaleidoscopic (Costar (Prelude t)) where
  kaleidoAct @p @a (Costar g) = Costar (\(Prelude tpa) -> repMap @p (g . Prelude) (unwrapRep (P.traverse (WrapRep @p @a) tpa)))

-- * The cotraversal

-- | The cotraversal flavor: pass any 'Cotraversable' carrier through the witness pair. The exact
-- mirror of 'Proarrow.Optic.Traversal.MonTravFl', with witness and carrier swapped.
type CotravFl :: forall {k}. FLAVOR k k
class (SetterFl p q) => CotravFl (p :: k +-> k) (q :: k +-> k) where
  cotravP :: (Cotraversable r) => p s a -> q b t -> r a b -> r s t
  default cotravP :: (KaleidoFl p q, Cotraversable r) => p s a -> q b t -> r a b -> r s t
  cotravP l r rab = unCotravAs (kaleidoP l r (CotravAs rab))

-- | The kaleidoscope flavor: act on any 'Kaleidoscopic' carrier through the witness pair.
type KaleidoFl :: forall {k}. FLAVOR k k
class (CotravFl p q) => KaleidoFl (p :: k +-> k) (q :: k +-> k) where
  kaleidoP :: (Kaleidoscopic r) => p s a -> q b t -> r a b -> r s t

-- | The generating witnesses: any representable 'StrongDistributiveProfunctor' -- any applicative
-- functor -- with its 'RepCostar'; the legs are @s ~> p % a@ and @p % b ~> t@.
instance (Representable p, StrongDistributiveProfunctor p) => CotravFl (p :: k +-> k) (RepCostar p)

instance (Representable p, StrongDistributiveProfunctor p) => KaleidoFl (p :: k +-> k) (RepCostar p) where
  kaleidoP l (RepCostar r) rab = dimap (index l) r (kaleidoAct @_ @p rab)

-- | The tensor-action pair for a monoid residual: @m ** -@ is the writer applicative.
instance
  (SymMonoidal k, HasCoproducts k, Monoid (m :: k))
  => CotravFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m))

instance
  (SymMonoidal k, HasCoproducts k, Monoid (m :: k))
  => KaleidoFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m))
  where
  kaleidoP (Rep h) (Corep i) rab = dimap h i (kaleidoAct @_ @(Rep (ActionAt Tensor m)) rab)

-- | The exponential pair for a comonoid exponent: @m ~~> -@ is the reader applicative. This is
-- what makes every 'Proarrow.Optic.Grate.Grate' a kaleidoscope.
instance (Closed k, SymMonoidal k, HasCoproducts k, Comonoid (m :: k)) => CotravFl (Rep (Exp m) :: k +-> k) (Corep (Exp m))

instance (Closed k, SymMonoidal k, HasCoproducts k, Comonoid (m :: k)) => KaleidoFl (Rep (Exp m) :: k +-> k) (Corep (Exp m)) where
  kaleidoP (Rep h) (Corep i) rab = dimap h i (kaleidoAct @_ @(Rep (Exp m)) rab)

instance (CategoryOf k) => CotravFl (Id :: k +-> k) (Id :: k +-> k) where
  cotravP (Id l) (Id r) = dimap l r
instance (CategoryOf k) => KaleidoFl (Id :: k +-> k) (Id :: k +-> k) where
  kaleidoP (Id l) (Id r) = dimap l r
instance (CotravFl f g, CotravFl f' g') => CotravFl (f :.: f') (g' :.: g) where
  cotravP (f :.: f') (g' :.: g) = cotravP @f @g f g . cotravP @f' @g' f' g'
instance (KaleidoFl f g, KaleidoFl f' g') => KaleidoFl (f :.: f') (g' :.: g) where
  kaleidoP (f :.: f') (g' :.: g) = kaleidoP @f @g f g . kaleidoP @f' @g' f' g'

instance SubFlavor CotravFl SetterFl where subFlavor r = r
instance SubFlavor KaleidoFl CotravFl where subFlavor r = r
instance SubFlavor KaleidoFl SetterFl where subFlavor r = r

type Cotraversal (s :: k) (t :: k) a b = Optic (Prostrong CotravFl) s t a b
type Cotraversal' s a = Cotraversal s s a a

type Kaleidoscope (s :: k) (t :: k) a b = Optic (Prostrong KaleidoFl) s t a b
type Kaleidoscope' s a = Kaleidoscope s s a a

-- | Build a cotraversal from its legs through an applicative functor, given as a representable
-- 'StrongDistributiveProfunctor' @p@.
cotraversal
  :: forall {k} p (s :: k) (t :: k) a b
   . (Representable p, StrongDistributiveProfunctor p, Ob a, Ob b)
  => (s ~> p % a) -> (p % b ~> t) -> Cotraversal s t a b
cotraversal l r = legs2prof @CotravFl (tabulate @p l) (RepCostar @_ @p r)

-- | Build a kaleidoscope from the same legs.
kaleidoscope
  :: forall {k} p (s :: k) (t :: k) a b
   . (Representable p, StrongDistributiveProfunctor p, Ob a, Ob b)
  => (s ~> p % a) -> (p % b ~> t) -> Kaleidoscope s t a b
kaleidoscope l r = legs2prof @KaleidoFl (tabulate @p l) (RepCostar @_ @p r)

-- | Pass a 'Cotraversable' carrier through a cotraversal (or any stronger optic, in any encoding,
-- '(%)'-composites included).
cotraverseOf
  :: forall {k} c (s :: k) (t :: k) a b r
   . (CategoryOf k, Cotraversable r, (Ob a, Ob b) => c (ExOptic CotravFl a b))
  => Optic c s t a b -> r a b -> r s t
cotraverseOf o rab = withLegs @CotravFl o \l r -> cotravP l r rab

-- | Act on a 'Kaleidoscopic' carrier through a kaleidoscope (or any stronger optic, in any
-- encoding, '(%)'-composites included). At @'Costar' ('Prelude' [])@ this is the literature's
-- aggregation operator @>-@: from @[a] -> b@ to @[s] -> t@.
kaleidoscopeOf
  :: forall {k} c (s :: k) (t :: k) a b r
   . (CategoryOf k, Kaleidoscopic r, (Ob a, Ob b) => c (ExOptic KaleidoFl a b))
  => Optic c s t a b -> r a b -> r s t
kaleidoscopeOf o rab = withLegs @KaleidoFl o \l r -> kaleidoP l r rab

-- | The carriers as instances, so that an optic of these flavors composed with another flavor that
-- also runs at the carrier can be eliminated there directly.
instance (Traversable t, Representable t) => Prostrong CotravFl (RepCostar t) where
  proact (f :.: c :.: g) = cotravP f g c

instance (Traversable t, Representable t) => Prostrong KaleidoFl (RepCostar t) where
  proact (f :.: c :.: g) = kaleidoP f g c
instance (P.Traversable t) => Prostrong KaleidoFl (Costar (Prelude t)) where
  proact (f :.: c :.: g) = kaleidoP f g c
