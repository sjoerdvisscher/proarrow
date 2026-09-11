{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A __kaleidoscope__ is the optic that distributes an arbitrary 'MonoidalProfunctor' -- the
-- @Applicative@\/zip structure ('one' and '**') -- rather than the full
-- 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor' a
-- 'Proarrow.Optic.Traversal.Traversal' needs. Where a
-- traversal /decomposes/ a whole into its foci, a kaleidoscope /also aggregates/: it can combine
-- the foci with @**@ (and 'one' for the empty case), not just replace them.
--
-- The witnesses here ('Two', 'Pow' @n@) present @s@ as a fixed tensor /power/ of the focus
-- (@s ~> a ** ... ** a@), which is a genuine decomposition -- so this kaleidoscope is really a
-- __fixed-arity 'Proarrow.Optic.Traversal.Traversal'__ (@'KaleidoFl' <: 'TravFl'@, so it
-- folds and sets like any traversal). Its /distinctive/ power is that 'kaleidoP' distributes an
-- arbitrary 'MonoidalProfunctor', including the non-'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor' ones (e.g.
-- @Costar f@) a traversal can't touch -- that is where the aggregation lives.
--
-- Crucially the aggregation is stated over an abstract @'MonoidalProfunctor' r@, /not/ the
-- Hask-specific @Costar f = f a -> b@: 'kaleidoscopeOf' works at any monoidal profunctor carrier
-- (the hom @('~>')@ gives 'Proarrow.Optic.Setter.over'; an applicative @'Proarrow.Profunctor.Instance.Star.Star' f@ combines the
-- foci through @f@).
--
-- Two witness families are provided: @'Two'@ (the ergonomic binary case, @s ~> a ** a@) and the
-- general @'Pow' n@ (the @n@-fold tensor power @s ~> 'Tensor' n a@, for any Peano 'Nat' arity),
-- alongside 'Id' (unary) and composition. @'Two'@ is @'Pow'@ at arity two up to the right
-- unitor.
module Proarrow.Optic.Kaleidoscope
  ( KaleidoFl (..)
  , Kaleidoscope
  , Kaleidoscope'
  , Two (..)
  , CoTwo (..)
  , kaleidoscope
  , kaleidoscopeOf

    -- * @n@-ary aggregation
  , Nat (..)
  , Tensor
  , KnownNat (..)
  , Pow (..)
  , CoPow (..)
  , kaleidoscopeN
  ) where

import Data.Kind (Constraint)
import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), type (**))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard, discard, fst, snd, (&&&))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
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
import Proarrow.Optic.Setter (SetterFl (..))
import Proarrow.Optic.Traversal (MonTravFl (..), TravFl (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

-- | The kaleidoscope flavor: distribute any 'MonoidalProfunctor' @r@ through the witness pair.
-- 'Proarrow.Optic.Traversal.TravFl' is a superclass: every kaleidoscope witness is a traversal
-- witness (instantiate @r@ at a 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor', a special 'MonoidalProfunctor'),
-- so a kaleidoscope folds, sets, and traverses. The extra power is distributing the /non/-SDP
-- monoidal profunctors as well.
type KaleidoFl :: forall {k}. FLAVOR k k
class (MonTravFl p q, GrateFl p q) => KaleidoFl (p :: k +-> k) (q :: k +-> k) where
  kaleidoP :: (MonoidalProfunctor r) => p s a -> q b t -> r a b -> r s t

instance (CategoryOf k) => KaleidoFl (Id :: k +-> k) (Id :: k +-> k) where
  kaleidoP (Id l) (Id r) = dimap l r
instance (KaleidoFl f g, KaleidoFl f' g') => KaleidoFl (f :.: f') (g' :.: g) where
  kaleidoP (f :.: f') (g' :.: g) = kaleidoP @f @g f g . kaleidoP @f' @g' f' g'

-- | The binary aggregation witness: @s@ presents two foci via the tensor.
type Two :: forall {k}. k +-> k
data Two s a where
  Two :: (Ob a) => (s ~> (a ** a)) -> Two s a

-- | The dual of 'Two': @t@ is rebuilt from two foci via the tensor.
type CoTwo :: forall {k}. k +-> k
data CoTwo b t where
  CoTwo :: (Ob b) => ((b ** b) ~> t) -> CoTwo b t

instance (Monoidal k) => Profunctor (Two :: k +-> k) where
  dimap l r (Two sa) = Two ((r ** r) . sa . l) \\ l \\ r
  r \\ Two sa = r \\ sa
instance (Monoidal k) => Profunctor (CoTwo :: k +-> k) where
  dimap l r (CoTwo bt) = CoTwo (r . bt . (l ** l)) \\ l \\ r
  r \\ CoTwo bt = r \\ bt

instance (Monoidal k) => SetterFl (Two :: k +-> k) (CoTwo :: k +-> k) where
  overP (Two sl) (CoTwo rt) f = rt . (f ** f) . sl
instance (Monoidal k) => FoldFl (Two :: k +-> k) (CoTwo :: k +-> k) where
  foldMapP (Two sl) am = mappend . (am ** am) . sl
instance (Monoidal k) => TravFl (Two :: k +-> k) (CoTwo :: k +-> k)
instance (Monoidal k) => MonTravFl (Two :: k +-> k) (CoTwo :: k +-> k) where
  monTravP (Two sl) (CoTwo rt) rab = dimap sl rt (rab ** rab)
instance (CopyDiscard k) => GrateFl (Two :: k +-> k) (CoTwo :: k +-> k) where
  zipWithP (Two @a sl) (CoTwo rt) @x kk = rt . (kk ** kk) . ((fst @a @a ^^^ obj @x) &&& (snd @a @a ^^^ obj @x)) . (sl ^^^ obj @x)
instance (CopyDiscard k) => KaleidoFl (Two :: k +-> k) (CoTwo :: k +-> k) where
  kaleidoP (Two sl) (CoTwo rt) rab = dimap sl rt (rab ** rab)
instance (Monoidal k) => Proadjunction (Two :: k +-> k) CoTwo where
  unit @x = withOb2 @k @x @x (CoTwo id :.: Two id)
  counit (Two sl :.: CoTwo rt) = rt . sl

instance SubFlavor KaleidoFl MonTravFl where subFlavor r = r
instance SubFlavor KaleidoFl GrateFl where subFlavor r = r
instance SubFlavor KaleidoFl TravFl where subFlavor r = r
instance SubFlavor KaleidoFl FoldFl where subFlavor r = r
instance SubFlavor KaleidoFl SetterFl where subFlavor r = r

type Kaleidoscope (s :: k) (t :: k) a b = Optic (Prostrong KaleidoFl) s t a b
type Kaleidoscope' s a = Kaleidoscope s s a a

-- | Build a binary kaleidoscope from a tensor decomposition of @s@ and recomposition of @t@.
kaleidoscope
  :: forall {k} (s :: k) (t :: k) a b
   . (CopyDiscard k, Ob a, Ob b)
  => (s ~> (a ** a)) -> ((b ** b) ~> t) -> Kaleidoscope s t a b
kaleidoscope sl rt = legs2prof @KaleidoFl (Two sl) (CoTwo rt)

-- | Distribute any 'MonoidalProfunctor' through a kaleidoscope (or any stronger optic). At the
-- hom @('~>')@ this is 'Proarrow.Optic.Setter.over'; at an applicative @'Proarrow.Profunctor.Instance.Star.Star' f@ the foci are
-- combined through @f@.
--
-- Accepts any encoding (cf. 'Proarrow.Optic.Traversal.traverseOf'), including '(%)'-composites.
kaleidoscopeOf
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, MonoidalProfunctor r, (Ob a, Ob b) => c (ExOptic KaleidoFl a b))
  => Optic c s t a b -> r a b -> r s t
kaleidoscopeOf o rab = withLegs @KaleidoFl o \l r -> kaleidoP l r rab

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
-- @n@-ary kaleidoscope.
type KnownNat :: Nat -> Constraint
class KnownNat (n :: Nat) where
  powDist :: (MonoidalProfunctor r) => r a b -> r (Tensor n a) (Tensor n b)

  -- | Collapse the @n@-fold tensor power of a monoid via 'mappend'\/'mempty'.
  powFold :: (Monoid m) => Tensor n m ~> m

  -- | Distribute the internal hom over the tensor power: split @x ~~> aⁿ@ into @(x ~~> a)ⁿ@ using
  -- 'CopyDiscard' projections. The @n@-fold form of the 'Two' split -- this is what makes an
  -- @n@-ary kaleidoscope a 'Proarrow.Optic.Grate.Grate'.
  splitPow :: forall k (x :: k) a. (Closed k, CopyDiscard k, Ob x, Ob a) => (x ~~> Tensor n a) ~> Tensor n (x ~~> a)

  -- | @Tensor n a@ is an object whenever @a@ is.
  withObTensor :: forall k (a :: k) r. (Monoidal k, Ob a) => ((Ob (Tensor n a)) => r) -> r

instance KnownNat Z where
  powDist _ = one
  powFold = mempty
  splitPow @k @x = withObExp @k @x @Unit (discard @k @(x ~~> Unit))
  withObTensor r = r
instance (KnownNat n) => KnownNat (S n) where
  powDist rab = rab ** powDist @n rab
  powFold @m = mappend . ((id :: m ~> m) ** powFold @n @m)
  splitPow @k @x @a =
    withObTensor @n @k @a
      ((fst @a @(Tensor n a) ^^^ obj @x) &&& (splitPow @n @k @x @a . (snd @a @(Tensor n a) ^^^ obj @x)))
  withObTensor @k @a r = withObTensor @n @k @a (withOb2 @k @a @(Tensor n a) r)

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
instance (CopyDiscard k, KnownNat n) => GrateFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  zipWithP (Pow @_ @_ @a sl) (CoPow rt) @x kk = rt . powDist @n kk . splitPow @n @_ @x @a . (sl ^^^ obj @x)
instance (CopyDiscard k, KnownNat n) => KaleidoFl (Pow n :: k +-> k) (CoPow n :: k +-> k) where
  kaleidoP (Pow sl) (CoPow rt) rab = dimap sl rt (powDist @n rab)
instance (Monoidal k, KnownNat n) => Proadjunction (Pow n :: k +-> k) (CoPow n) where
  unit @x = (CoPow id :.: Pow id) \\ powDist @n (id :: x ~> x)
  counit (Pow sl :.: CoPow rt) = rt . sl

-- | Build an @n@-ary kaleidoscope from a tensor-power decomposition of @s@ and recomposition of
-- @t@. @'kaleidoscope'@ is the arity-two case.
kaleidoscopeN
  :: forall {k} (n :: Nat) (s :: k) (t :: k) a b
   . (CopyDiscard k, KnownNat n, Ob a, Ob b)
  => (s ~> Tensor n a) -> (Tensor n b ~> t) -> Kaleidoscope s t a b
kaleidoscopeN sl rt = legs2prof @KaleidoFl (Pow @n sl) (CoPow @n rt)
