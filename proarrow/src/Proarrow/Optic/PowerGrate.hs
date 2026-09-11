{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A __power grate__ is a 'Proarrow.Optic.Grate.Grate' whose exponent is a fixed tensor /power/ of
-- the focus: the witness @'Pow' n@ presents @s@ as @a ** ... ** a@ (@n@ times), i.e. the exponential
-- by a finite arity, which is also the reader applicative for @n@ readers. That fixed, finite shape
-- is a genuine decomposition, so a power grate is also a __fixed-arity
-- 'Proarrow.Optic.Traversal.Traversal'__ (@'PowerGrateFl' <: 'GrateFl', 'KaleidoFl', 'MonTravFl'@):
-- it zips, aggregates, folds, sets and traverses like those do.
--
-- Its /distinctive/ power over a grate or kaleidoscope is the eliminator: 'powerGrateP' distributes
-- an arbitrary 'MonoidalProfunctor' -- the @Applicative@\/zip structure ('one' and '**') alone --
-- rather than the full 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor' a
-- traversal needs or the traversable carrier a kaleidoscope needs. With a fixed arity, /any/ functor
-- carrier @Costar f@ distributes, by unzipping @f (a ** ... ** a)@ into @f a ** ... ** f a@.
--
-- The aggregation is stated over an abstract @'MonoidalProfunctor' r@, /not/ the Hask-specific
-- @Costar f = f a -> b@: 'powerGrateOf' works at any monoidal profunctor carrier (the hom @('~>')@
-- gives 'Proarrow.Optic.Setter.over'; an applicative @'Proarrow.Profunctor.Instance.Star.Star' f@
-- combines the foci through @f@).
module Proarrow.Optic.PowerGrate
  ( PowerGrateFl (..)
  , PowerGrate
  , PowerGrate'
  , powerGrateOf
  , zipWithOf

    -- * @n@-ary aggregation
  , Nat (..)
  , Tensor
  , KnownNat (..)
  , Pow (..)
  , CoPow (..)
  , powerGrate
  ) where

import Data.Kind (Constraint)
import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, swapInner, type (**))
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Action (CoprodAction)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..), fst, snd, (&&&))
import Proarrow.Category.Monoidal.Distributive (Traversable (..))
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Colimit.BinaryCoproduct (COPROD (..), Coprod (..), HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (//), (\\), type (+->))
import Proarrow.Functor (Functor)
import Proarrow.Limit.BinaryProduct (Cartesian)
import Proarrow.Monoid (Monoid (..))
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Optic
  , Prostrong (..)
  , SubFlavor (..)
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.Fold (FoldFl (..))
import Proarrow.Optic.Grate (GrateFl (..))
import Proarrow.Optic.Kaleidoscope (CotravFl, KaleidoFl (..), Kaleidoscopic (..), kaleidoscopeOf)
import Proarrow.Optic.Setter (SetterFl (..))
import Proarrow.Optic.Traversal (MonTravFl (..), TravFl (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Costar (Costar)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (RepCostar (..), Representable (..))

-- | The power-grate flavor: distribute any 'MonoidalProfunctor' @r@ through the witness
-- pair. 'Proarrow.Optic.Traversal.TravFl' is a superclass: every power-grate witness is a
-- traversal witness (instantiate @r@ at a 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor',
-- a special 'MonoidalProfunctor'), so it folds, sets, and traverses. The extra power is
-- distributing the /non/-SDP monoidal profunctors as well. 'Proarrow.Optic.Kaleidoscope.KaleidoFl'
-- is a superclass too: a tensor power is an applicative functor (the reader applicative).
type PowerGrateFl :: forall {k}. FLAVOR k k
class (MonTravFl p q, GrateFl p q) => PowerGrateFl (p :: k +-> k) (q :: k +-> k) where
  powerGrateP :: (MonoidalProfunctor r) => p s a -> q b t -> r a b -> r s t

instance (CategoryOf k) => PowerGrateFl (Id :: k +-> k) (Id :: k +-> k) where
  powerGrateP (Id l) (Id r) = dimap l r
instance (PowerGrateFl f g, PowerGrateFl f' g') => PowerGrateFl (f :.: f') (g' :.: g) where
  powerGrateP (f :.: f') (g' :.: g) = powerGrateP @f @g f g . powerGrateP @f' @g' f' g'

-- | The carrier of the literature's kaleidoscope eliminator (@>-@): @'Costar' f@, i.e. @f a -> b@ for
-- any functor @f@ on a cartesian category. Power grates distribute any 'MonoidalProfunctor', and
-- @'Costar' f@ is one, so this is 'powerGrateP' at that carrier; it exists as an instance (rather than
-- only through 'powerGrateOf') so that a power grate composed with another flavor that also runs
-- at @Costar f@ -- an algebraic lens, say -- can be eliminated there directly.
instance (Cartesian k, Functor (f :: k -> k)) => Prostrong PowerGrateFl (Costar f :: k +-> k) where
  proact (f :.: c :.: g) = powerGrateP f g c

instance SubFlavor PowerGrateFl MonTravFl where subFlavor r = r
instance SubFlavor PowerGrateFl KaleidoFl where subFlavor r = r
instance SubFlavor PowerGrateFl CotravFl where subFlavor r = r
instance SubFlavor PowerGrateFl GrateFl where subFlavor r = r
instance SubFlavor PowerGrateFl TravFl where subFlavor r = r
instance SubFlavor PowerGrateFl FoldFl where subFlavor r = r
instance SubFlavor PowerGrateFl SetterFl where subFlavor r = r

type PowerGrate (s :: k) (t :: k) a b = Optic (Prostrong PowerGrateFl) s t a b
type PowerGrate' s a = PowerGrate s s a a

-- | Distribute any 'MonoidalProfunctor' through a power grate (or any stronger optic). At the
-- hom @('~>')@ this is 'Proarrow.Optic.Setter.over'; at an applicative @'Proarrow.Profunctor.Instance.Star.Star' f@ the foci are
-- combined through @f@.
--
-- Accepts any encoding (cf. 'Proarrow.Optic.Traversal.traverseOf'), including '(%)'-composites.
powerGrateOf
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, MonoidalProfunctor r, (Ob a, Ob b) => c (ExOptic PowerGrateFl a b))
  => Optic c s t a b -> r a b -> r s t
powerGrateOf o rab = withLegs @PowerGrateFl o \l r -> powerGrateP l r rab

-- * @n@-ary aggregation via tensor powers

-- | A Peano natural, the arity of a 'Pow' witness.
data Nat = Z | S Nat

-- | The @n@-fold tensor power of @a@: @a ** a ** ... ** a@ (@n@ times, terminated by 'Unit').
type Tensor :: Nat -> k -> k
type family Tensor n a where
  Tensor Z a = Unit
  Tensor (S n) a = a ** Tensor n a

-- | Distribute a 'MonoidalProfunctor' over the @n@-fold tensor power, by combining @n@ copies of
-- the carrier value with 'one' (at 'Z') and '**' (at 'S') -- the profunctor-general heart of the
-- @n@-ary power grate.
type KnownNat :: Nat -> Constraint
class KnownNat (n :: Nat) where
  powDist :: (MonoidalProfunctor r) => r a b -> r (Tensor n a) (Tensor n b)

  -- | Collapse the @n@-fold tensor power of a monoid via 'mappend'\/'mempty'.
  powFold :: (Monoid m) => Tensor n m ~> m

  -- | Distribute the internal hom over the tensor power: split @x ~~> aⁿ@ into @(x ~~> a)ⁿ@ using
  -- 'CopyDiscard' projections -- this is what makes an @n@-ary power grate a
  -- 'Proarrow.Optic.Grate.Grate'.
  splitPow :: forall k (x :: k) a. (Closed k, CopyDiscard k, Ob x, Ob a) => (x ~~> Tensor n a) ~> Tensor n (x ~~> a)

  -- | @Tensor n a@ is an object whenever @a@ is.
  withObTensor :: forall k (a :: k) r. (Monoidal k, Ob a) => ((Ob (Tensor n a)) => r) -> r

  -- | Zip two tensor powers into the tensor power of the tensor: the @<*>@ of the reader
  -- applicative @Tensor n@.
  powZip :: forall k (a :: k) c. (SymMonoidal k, Ob a, Ob c) => (Tensor n a ** Tensor n c) ~> Tensor n (a ** c)

  -- | @n@ copies of an object, via 'copy' and 'discard': the @pure@ of the reader applicative.
  powCopy :: forall k (a :: k). (CopyDiscard k, Ob a) => a ~> Tensor n a

  -- | The tensor power of the unit is (isomorphic to) the unit.
  powUnit :: forall k. (Monoidal k) => Unit ~> Tensor n (Unit :: k)

instance KnownNat Z where
  powDist _ = one
  powFold = mempty
  splitPow @k @x = withObExp @k @x @Unit (discard @k @(x ~~> Unit))
  withObTensor r = r
  powZip @k = leftUnitor @k @Unit
  powCopy @k @a = discard @k @a
  powUnit = id
instance (KnownNat n) => KnownNat (S n) where
  powDist rab = rab ** powDist @n rab
  powFold @m = mappend . ((id :: m ~> m) ** powFold @n @m)
  splitPow @k @x @a =
    withObTensor @n @k @a
      ((fst @a @(Tensor n a) ^^^ obj @x) &&& (splitPow @n @k @x @a . (snd @a @(Tensor n a) ^^^ obj @x)))
  withObTensor @k @a r = withObTensor @n @k @a (withOb2 @k @a @(Tensor n a) r)
  powZip @k @a @c =
    withObTensor @n @k @a
      (withObTensor @n @k @c (((obj @a ** obj @c) ** powZip @n @k @a @c) . swapInner @a @(Tensor n a) @c @(Tensor n c)))
  powCopy @k @a = (obj @a ** powCopy @n @k @a) . copy @k @a
  powUnit @k = (obj @(Unit :: k) ** powUnit @n @k) . leftUnitorInv @k @Unit

-- | The arity-@n@ aggregation witness: @s@ presents @n@ foci via the tensor power.
type Pow :: forall {k}. Nat -> k +-> k
data Pow n s a where
  Pow :: forall (n :: Nat) {k} (s :: k) (a :: k). (Ob a) => (s ~> Tensor n a) -> Pow n s a

-- | The dual of 'Pow': @t@ is rebuilt from @n@ foci.
type CoPow :: forall {k}. Nat -> k +-> k
data CoPow n b t where
  CoPow :: forall (n :: Nat) {k} (b :: k) (t :: k). (Ob b) => (Tensor n b ~> t) -> CoPow n b t

instance (Monoidal k, KnownNat n) => Profunctor (Pow n :: k +-> k) where
  dimap l r (Pow sa) = Pow (powDist @n r . sa . l) \\ l \\ r
  r \\ Pow sa = r \\ sa
instance (Monoidal k, KnownNat n) => Profunctor (CoPow n :: k +-> k) where
  dimap l r (CoPow bt) = CoPow (r . bt . powDist @n l) \\ l \\ r
  r \\ CoPow bt = r \\ bt

instance (Monoidal k, KnownNat n) => SetterFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  overP (Pow sl) (CoPow rt) f = rt . powDist @n f . sl
instance (Monoidal k, KnownNat n) => FoldFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  foldMapP (Pow sl) am = powFold @n . powDist @n am . sl
instance (Monoidal k, KnownNat n) => TravFl (Pow n :: k +-> k) (CoPow n :: k +-> k)
instance (Monoidal k, KnownNat n) => MonTravFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  monTravP (Pow sl) (CoPow rt) rab = dimap sl rt (powDist @n rab)
instance (CopyDiscard k, HasCoproducts k, KnownNat n) => GrateFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  zipWithP (Pow @_ @_ @a sl) (CoPow rt) @x kk = rt . powDist @n kk . splitPow @n @_ @x @a . (sl ^^^ obj @x)
instance (CopyDiscard k, HasCoproducts k, KnownNat n) => PowerGrateFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  powerGrateP (Pow sl) (CoPow rt) rab = dimap sl rt (powDist @n rab)

-- | @'Pow' n@ is the representable profunctor of the tensor power @Tensor n@, which is the reader
-- applicative for @n@ readers; the instances below make it a
-- 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor', hence a kaleidoscope
-- witness.
-- | A tensor power is a fixed-shape traversable: distribute the carrier over the @n@ copies.
instance (Monoidal k, KnownNat n) => Traversable (Pow n :: k +-> k) where
  traverse @_ @_ @b (Pow f :.: p) = p // withObTensor @n @k @b (lmap f (powDist @n p) :.: Pow id)

instance (Monoidal k, KnownNat n) => Representable (Pow n :: k +-> k) where
  type Pow n % a = Tensor n a
  index (Pow f) = f
  tabulate = Pow
  repMap = powDist @n

instance (SymMonoidal k, KnownNat n) => MonoidalProfunctor (Pow n :: k +-> k) where
  one = Pow (powUnit @n)
  Pow @_ @_ @a f ** Pow @_ @_ @c g = f // g // withOb2 @k @a @c (Pow (powZip @n @k @a @c . (f ** g)))
instance (SymMonoidal k, HasCoproducts k, KnownNat n) => MonoidalProfunctor (Coprod (Pow n :: k +-> k)) where
  one = withObTensor @n @k @InitialObject (Coprod (Pow initiate))
  Coprod (Pow @_ @_ @a f) ** Coprod (Pow @_ @_ @c g) =
    withObCoprod @k @a @c (Coprod (Pow (powDist @n (lft @k @a @c) . f ||| powDist @n (rgt @k @a @c) . g)))
instance (CopyDiscard k, KnownNat n) => Strong M.Tensor (Pow n :: k +-> k) where
  act @x (Pow @_ @_ @a f) = f // withOb2 @k @x @a (Pow (powZip @n @k @x @a . (powCopy @n @k @x ** f)))
instance (CopyDiscard k, HasCoproducts k, KnownNat n) => Strong CoprodAction (Pow n :: k +-> k) where
  act @(COPR x) (Pow @_ @_ @a f) =
    f // withObCoprod @k @x @a (Pow (powDist @n (lft @k @x @a) . powCopy @n @k @x ||| powDist @n (rgt @k @x @a) . f))
instance (CopyDiscard k, HasCoproducts k, KnownNat n) => CotravFl (Pow n :: k +-> k) (CoPow n :: k +-> k)
instance (CopyDiscard k, HasCoproducts k, KnownNat n) => KaleidoFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  kaleidoP (Pow sl) (CoPow rt) rab = dimap sl rt (kaleidoAct @_ @(Pow n) rab)
instance (Monoidal k, KnownNat n) => Proadjunction (Pow n :: k +-> k) (CoPow n) where
  unit @x = (CoPow id :.: Pow id) \\ powDist @n (id :: x ~> x)
  counit (Pow sl :.: CoPow rt) = rt . sl

-- | Build an @n@-ary power grate from a tensor-power decomposition of @s@ and recomposition
-- of @t@.
powerGrate
  :: forall {k} (n :: Nat) (s :: k) (t :: k) a b
   . (CopyDiscard k, HasCoproducts k, KnownNat n, Ob a, Ob b)
  => (s ~> Tensor n a) -> (Tensor n b ~> t) -> PowerGrate s t a b
powerGrate sl rt = legs2prof @PowerGrateFl (Pow @n sl) (CoPow @n rt)

-- | Zip two sources through a 'Proarrow.Optic.Kaleidoscope.Kaleidoscope' (or any stronger optic, a
-- 'Proarrow.Optic.Grate.Grate' in particular, in any encoding): combine the foci pairwise. This is
-- 'kaleidoscopeOf' at the carrier @'RepCostar' ('Pow' 2)@, the costar of the binary tensor power --
-- a binary combination @(a ** a) ~> b@ of foci, which the optic's applicative lifts by @liftA2@.
zipWithOf
  :: forall {k} c (s :: k) (t :: k) a b
   . (Monoidal k, Ob a, (Ob a, Ob b) => c (ExOptic KaleidoFl a b))
  => Optic c s t a b -> ((a ** a) ~> b) -> (s ** s) ~> t
zipWithOf o f =
  case kaleidoscopeOf o (RepCostar @_ @(Pow (S (S Z))) (f . (obj @a ** rightUnitor @k @a))) of
    RepCostar @s' g -> g . (obj @s' ** rightUnitorInv @k @s')
