{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __traversal__: the many-focus optic, distributing any
-- 'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor' with product strength
-- through the foci. This module keeps the mutually-recursive 'TravRes'\/'MonTravRes' flavor
-- classes and their leaf witnesses ('Traversable' and 'Cotraversable' functors, the product lens,
-- the coproduct prism, 'Beside'\/'BesideSum' juxtaposition and the unit\/zero witnesses); the
-- free-profunctor apparatus lives in "Proarrow.Optic.MonoidalTraversal". A traversal subtypes to
-- 'Proarrow.Optic.Fold.Fold' and 'Proarrow.Optic.Setter.Setter'. Build with 'traversed' (from a
-- 'Traversable') or 'Proarrow.Optic.MonoidalTraversal.traversal' (from the van-Laarhoven form),
-- eliminate with 'traverseOf'.
module Proarrow.Optic.Traversal where

import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Instance.Product (Diag, (:**:) (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), MultRep, Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt, CoprodAction, ProdAction)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Distributive
  ( Bicartesian
  , Cotraversable (..)
  , Distributive
  , StrongDistributiveProfunctor
  , Traversable (..)
  , corepTraverse
  , repTraverse
  )
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Coproduct
  , HasBinaryCoproducts (..)
  , HasCoproducts
  , PlusRep
  , nil
  , (++)
  )
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), PROD (..), Product)
import Proarrow.Monoid (Comonoid, Monoid (..))
import Proarrow.Monoid qualified as Mon
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Optic
  , Prostrong (..)
  , SubFlavor (..)
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.Fold (FoldRes (..))
import Proarrow.Optic.Setter (SetterRes (..))
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..), coindex)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), RepCostar (..), Representable (..))

type TravRes :: forall {k}. FLAVOR k k
class (SetterRes p q, FoldRes p q) => TravRes (p :: k +-> k) (q :: k +-> k) where
  -- | Distribute a traversal-strength profunctor. Only the product-lens witness genuinely needs
  -- @'Strong' 'ProdAction'@ (to carry the residual through the categorical product); every other
  -- witness distributes a plain 'StrongDistributiveProfunctor' and inherits 'travP' from 'monTravP'.
  travP :: (StrongDistributiveProfunctor r, Strong ProdAction r) => p s a -> q b t -> r a b -> r s t
  default travP :: (MonTravRes p q, StrongDistributiveProfunctor r) => p s a -> q b t -> r a b -> r s t
  travP = monTravP

-- | A __monoidal traversal__ sits between 'Proarrow.Optic.Kaleidoscope.Kaleidoscope' and
-- 'Traversal': it distributes any 'StrongDistributiveProfunctor' without the product-strength a
-- lens-as-traversal needs. Every traversal witness except the product lens is a monoidal traversal.
type MonTravRes :: forall {k}. FLAVOR k k
class (TravRes p q) => MonTravRes (p :: k +-> k) (q :: k +-> k) where
  monTravP :: (StrongDistributiveProfunctor r) => p s a -> q b t -> r a b -> r s t

instance (Bicartesian k, Traversable t, Representable t) => TravRes (t :: k +-> k) (RepCostar t)
instance (Bicartesian k, Traversable t, Representable t) => MonTravRes (t :: k +-> k) (RepCostar t) where
  monTravP l (RepCostar r) = dimap (index l) r . repTraverse @t

-- | The former cotraversal witness: a corepresentable 'Cotraversable' functor builds @s@ from a
-- shape of @a@'s. Its 'travP' distributes an SDP exactly as the old @cotravP@ did -- for these
-- (representable) witnesses a cotraversal /is/ a traversal, which is why there is no separate
-- @Cotraversal@ optic.
instance (Bicartesian k, Cotraversable t, Corepresentable t) => TravRes (CorepStar t) (t :: k +-> k)

instance (Bicartesian k, Cotraversable t, Corepresentable t) => MonTravRes (CorepStar t) (t :: k +-> k) where
  monTravP (CorepStar l) co = dimap l (coindex co) . corepTraverse @t

instance (HasBinaryProducts k, Ob (s :: k)) => TravRes (Rep (Product s)) (Corep (Product s)) where
  travP (Rep p) (Corep q) r = dimap p q (act @ProdAction @_ @(PR s) r)

-- | The tensor-action witness pair @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' m)@ with a __comonoid__
-- residual @m@ (legs @s ~> m ** a@, @m ** b ~> t@) is a (monoidal) traversal witness: it folds by
-- discarding the residual with the comonoid's counit and distributes any 'StrongDistributiveProfunctor'
-- through @'act' \@'Tensor'@ -- exactly the strength such a profunctor already carries, so no product
-- strength or @tensor = product@ is needed. Asking 'Comonoid' of the residual only (rather than
-- 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' of the whole category) is what makes this work
-- in @LINEAR@ for the duplicable objects; it is also the monoidal-lens witness
-- ("Proarrow.Optic.MonoidalLens").
instance (Comonoid (m :: k)) => FoldRes (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  foldMapP (Rep h) am = leftUnitor . (Mon.counit @m ** am) . h

instance (Comonoid (m :: k)) => TravRes (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m))
instance (Comonoid (m :: k)) => MonTravRes (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  monTravP (Rep h) (Corep i) r = dimap h i (act @Tensor @_ @m r)
instance (CopyDiscard k, HasCoproducts k, Ob t) => TravRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t))
instance (CopyDiscard k, HasCoproducts k, Ob t) => MonTravRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  monTravP (Rep p) (Corep q) r = dimap p q (act @CoprodAction @_ @(COPR t) r)
instance (CategoryOf k) => TravRes (Id :: k +-> k) (Id :: k +-> k)
instance (CategoryOf k) => MonTravRes (Id :: k +-> k) (Id :: k +-> k) where
  monTravP (Id l) (Id r) = dimap l r
instance (TravRes f g, TravRes f' g') => TravRes (f :.: f') (g' :.: g) where
  travP (f :.: f') (g' :.: g) = travP @f @g f g . travP @f' @g' f' g'
instance (MonTravRes f g, MonTravRes f' g') => MonTravRes (f :.: f') (g' :.: g) where
  monTravP (f :.: f') (g' :.: g) = monTravP @f @g f g . monTravP @f' @g' f' g'

instance SubFlavor TravRes SetterRes where subFlavor r = r
instance SubFlavor TravRes FoldRes where subFlavor r = r
instance SubFlavor MonTravRes TravRes where subFlavor r = r
instance SubFlavor MonTravRes SetterRes where subFlavor r = r
instance SubFlavor MonTravRes FoldRes where subFlavor r = r

type Traversal (s :: k) (t :: k) a b = Optic (Prostrong TravRes) s t a b
type Traversal' s a = Traversal s s a a

-- | Traverse: distribute any 'StrongDistributiveProfunctor' -- not merely a @Star f@ (the
-- Hask van-Laarhoven shape) -- through any optic that is at least a 'Traversal'. Works for an
-- arbitrary profunctor carrier by handing it to 'travP', rather than relying on a per-carrier
-- @'Prostrong' w p@ bridge (which could only ever cover specific carrier heads).
--
-- The optic is accepted in any encoding: the constraint asks the optic's class to hold for the
-- generic carrier @'ExOptic' 'TravRes' a b@, which a 'Prostrong'-flavored optic discharges via
-- @'SubFlavor' w 'TravRes'@, a '(%)'-composite one conjunct at a time, and a profunctor-class one
-- ('Proarrow.Optic.MonoidalTraversal.PTraversalFull') through the carrier's by-generator instances.
traverseOf
  :: forall {k} c (s :: k) (t :: k) a b p
   . (Distributive k, StrongDistributiveProfunctor p, Strong ProdAction p, (Ob a, Ob b) => c (ExOptic TravRes a b))
  => Optic c s t a b -> p a b -> p s t
traverseOf o pab = withLegs @TravRes o \l r -> travP l r pab

-- | Build a traversal from a 'Traversable' (representable) functor @t@: it focuses every element
-- the functor holds. This is the one weak-flavor builder that is genuinely primitive -- a
-- 'Traversable's traversal is not reachable by 'convert' from any single stronger optic. The
-- witness is @t@ itself paired with @'RepCostar' t@ (see 'TravRes' above); the two legs are the
-- representable universal @'repUniv'@ and the identity 'RepCostar'.
traversed
  :: forall {k} (t :: k +-> k) a b
   . (Bicartesian k, Traversable t, Representable t, Ob a, Ob b) => Traversal (t % a) (t % b) a b
traversed = legs2prof @TravRes (repUniv @t) (corepUniv @(RepCostar t))

-- * The free traversal profunctor

-- | Witness pair for traversing two juxtaposed (tensored) parts in sequence, both parts focusing
-- the same type @x@:
--
-- > Beside p1 p2 s x = exists s1 s2. (s ~> s1 ** s2, p1 s1 x, p2 s2 x)
--
-- spelled as a composite through the product category @(k, k)@: decompose the source with the
-- tensor (@'Rep' 'MultRep'@, @s ~> s1 ** s2@), run the two witnesses side by side (':**:'), and
-- identify their foci with the diagonal (@'Rep' 'Diag'@, @'(x1, x2) ~> '(x, x)@). Compare
-- 'Proarrow.Profunctor.Instance.Day.Day', which is the same composite with @'Corep' 'MultRep'@ in
-- place of the diagonal, so that the two foci are /tensored/ (@x1 ** x2@) instead of identified.
-- The identification is essential: a @(Day p1 p2, Day q1 q2)@ witness pair admits no componentwise
-- 'travP' (it would have to split a 'StrongDistributiveProfunctor' value at a tensor), which is why
-- 'Proarrow.Optic.Day.DayRes'-flavored optics focus /pairs/ while this one visits both foci in
-- sequence.
type Beside :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
type Beside p1 p2 = Rep MultRep :.: (p1 :**: p2) :.: Rep Diag

-- | The covariant half of the 'Beside' witness pair: duplicate the focus with the diagonal
-- (@'Corep' 'Diag'@), run the two witnesses side by side, recompose the targets with the tensor
-- (@'Corep' 'MultRep'@, @t1 ** t2 ~> t@).
type CoBeside :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
type CoBeside q1 q2 = Corep Diag :.: (q1 :**: q2) :.: Corep MultRep

instance (SetterRes p1 q1, SetterRes p2 q2, Monoidal k) => SetterRes (Beside p1 p2 :: k +-> k) (CoBeside q1 q2) where
  overP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) (Corep (g1 :**: g2) :.: (r1 :**: r2) :.: Corep c) f =
    c . (overP @p1 @q1 (rmap f1 l1) (lmap g1 r1) f ** overP @p2 @q2 (rmap f2 l2) (lmap g2 r2) f) . d
instance (FoldRes p1 q1, FoldRes p2 q2, Monoidal k) => FoldRes (Beside p1 p2 :: k +-> k) (CoBeside q1 q2 :: k +-> k) where
  foldMapP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) am =
    mappend . (foldMapP @p1 @q1 (rmap f1 l1) am ** foldMapP @p2 @q2 (rmap f2 l2) am) . d
instance (TravRes p1 q1, TravRes p2 q2, Monoidal k) => TravRes (Beside p1 p2 :: k +-> k) (CoBeside q1 q2) where
  travP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) (Corep (g1 :**: g2) :.: (r1 :**: r2) :.: Corep c) r =
    dimap d c (travP @p1 @q1 (rmap f1 l1) (lmap g1 r1) r ** travP @p2 @q2 (rmap f2 l2) (lmap g2 r2) r)
instance (MonTravRes p1 q1, MonTravRes p2 q2, Monoidal k) => MonTravRes (Beside p1 p2 :: k +-> k) (CoBeside q1 q2) where
  monTravP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) (Corep (g1 :**: g2) :.: (r1 :**: r2) :.: Corep c) r =
    dimap d c (monTravP @p1 @q1 (rmap f1 l1) (lmap g1 r1) r ** monTravP @p2 @q2 (rmap f2 l2) (lmap g2 r2) r)

-- | Witness pair for traversing one of two alternative (coproduct) parts: 'Beside' with the tensor
-- replaced by the coproduct (@'Rep' 'PlusRep'@, @s ~> s1 || s2@, and @'Corep' 'PlusRep'@,
-- @t1 || t2 ~> t@). Here identifying the foci and tensoring them agree -- @x1 || x2 ~> x@ /is/ a pair
-- @(x1 ~> x, x2 ~> x)@ -- so this is literally Day convolution over the coproduct.
type BesideSum :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
type BesideSum p1 p2 = Rep PlusRep :.: (p1 :**: p2) :.: Rep Diag

-- | The covariant half of the 'BesideSum' witness pair.
type CoBesideSum :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
type CoBesideSum q1 q2 = Corep Diag :.: (q1 :**: q2) :.: Corep PlusRep

instance (SetterRes p1 q1, SetterRes p2 q2, HasBinaryCoproducts k) => SetterRes (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2) where
  overP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) (Corep (g1 :**: g2) :.: (r1 :**: r2) :.: Corep c) f =
    c . (overP @p1 @q1 (rmap f1 l1) (lmap g1 r1) f +++ overP @p2 @q2 (rmap f2 l2) (lmap g2 r2) f) . d
instance
  (FoldRes p1 q1, FoldRes p2 q2, HasBinaryCoproducts k)
  => FoldRes (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2 :: k +-> k)
  where
  foldMapP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) am =
    (foldMapP @p1 @q1 (rmap f1 l1) am ||| foldMapP @p2 @q2 (rmap f2 l2) am) . d
instance (TravRes p1 q1, TravRes p2 q2, HasBinaryCoproducts k) => TravRes (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2) where
  travP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) (Corep (g1 :**: g2) :.: (r1 :**: r2) :.: Corep c) r =
    dimap d c (travP @p1 @q1 (rmap f1 l1) (lmap g1 r1) r ++ travP @p2 @q2 (rmap f2 l2) (lmap g2 r2) r)
instance
  (MonTravRes p1 q1, MonTravRes p2 q2, HasBinaryCoproducts k)
  => MonTravRes (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2)
  where
  monTravP (Rep d :.: (l1 :**: l2) :.: Rep (f1 :**: f2)) (Corep (g1 :**: g2) :.: (r1 :**: r2) :.: Corep c) r =
    dimap d c (monTravP @p1 @q1 (rmap f1 l1) (lmap g1 r1) r ++ monTravP @p2 @q2 (rmap f2 l2) (lmap g2 r2) r)

-- | Witness pair with no foci at all: decompose to 'Unit' and rebuild.
--
-- 'UnitW' and 'CoUnitW' are the two halves of 'Proarrow.Profunctor.Instance.Day.DayUnit', one
-- per side of the witness pair, with a phantom focus: together with 'Beside'\/'CoBeside' being
-- 'Proarrow.Profunctor.Instance.Day.Day' with the foci identified, the witness pairs here are exactly the
-- Day-monoidal structure on profunctors (@'Proarrow.Category.Monoidal.Monoidal' (j '+->' k)@),
-- split at the focus. The split is forced: a whole 'Proarrow.Profunctor.Instance.Day.DayUnit'
-- on the decomposition side would demand @Unit ~> a@ for an arbitrary focus @a@.
--
-- Unlike 'Beside', this cannot be spelled as a composite: the nullary analogue would pass through
-- the unit category @()@ (@'Rep' 'Proarrow.Category.Monoidal.UnitRep' :.: TerminalProfunctor@), but
-- @()@ can coincide with the ambient kind @k@, so its instances would overlap with the generic
-- composition instances -- whereas @(k, k)@ never equals @k@.
type UnitW :: forall {k}. k +-> k
data UnitW s x where
  UnitW :: (Ob x) => (s ~> Unit) -> UnitW s x

-- | The covariant half of the 'UnitW' witness pair: rebuilds the target from 'Unit'.
type CoUnitW :: forall {k}. k +-> k
data CoUnitW x t where
  CoUnitW :: (Ob x) => (Unit ~> t) -> CoUnitW x t

instance (Monoidal k) => Profunctor (UnitW :: k +-> k) where
  dimap l r (UnitW h) = UnitW (h . l) \\ r
  r \\ UnitW h = r \\ h
instance (Monoidal k) => Profunctor (CoUnitW :: k +-> k) where
  dimap l r (CoUnitW i) = CoUnitW (r . i) \\ l
  r \\ CoUnitW i = r \\ i

instance (Monoidal k) => SetterRes (UnitW :: k +-> k) CoUnitW where
  overP (UnitW h) (CoUnitW i) _ = i . h
instance (Monoidal k) => FoldRes (UnitW :: k +-> k) (CoUnitW :: k +-> k) where
  foldMapP (UnitW h) _ = mempty . h
instance (Monoidal k) => TravRes (UnitW :: k +-> k) CoUnitW
instance (Monoidal k) => MonTravRes (UnitW :: k +-> k) CoUnitW where
  monTravP (UnitW h) (CoUnitW i) _ = dimap h i one
instance (Monoidal k) => Proadjunction (UnitW :: k +-> k) CoUnitW where
  unit = CoUnitW id :.: UnitW id
  counit (UnitW h :.: CoUnitW i) = i . h

-- | Witness pair for the impossible case: decompose to the initial object -- the halves of the
-- (unspelled) unit of Day convolution over the coproduct monoidal structure, cf.
-- 'UnitW'\/'CoUnitW'.
type ZeroW :: forall {k}. k +-> k
data ZeroW s x where
  ZeroW :: (Ob x) => (s ~> InitialObject) -> ZeroW s x

-- | The covariant half of the 'ZeroW' witness pair: rebuilds the target from 'InitialObject'.
type CoZeroW :: forall {k}. k +-> k
data CoZeroW x t where
  CoZeroW :: (Ob x) => (InitialObject ~> t) -> CoZeroW x t

instance (HasInitialObject k) => Profunctor (ZeroW :: k +-> k) where
  dimap l r (ZeroW h) = ZeroW (h . l) \\ r
  r \\ ZeroW h = r \\ h
instance (HasInitialObject k) => Profunctor (CoZeroW :: k +-> k) where
  dimap l r (CoZeroW i) = CoZeroW (r . i) \\ l
  r \\ CoZeroW i = r \\ i

instance (HasInitialObject k) => SetterRes (ZeroW :: k +-> k) CoZeroW where
  overP (ZeroW h) (CoZeroW i) _ = i . h
instance (HasInitialObject k) => FoldRes (ZeroW :: k +-> k) (CoZeroW :: k +-> k) where
  foldMapP (ZeroW h) _ = initiate . h
instance (HasInitialObject k) => TravRes (ZeroW :: k +-> k) CoZeroW
instance (HasInitialObject k) => MonTravRes (ZeroW :: k +-> k) CoZeroW where
  monTravP (ZeroW h) (CoZeroW i) _ = dimap h i nil
instance (HasInitialObject k) => Proadjunction (ZeroW :: k +-> k) CoZeroW where
  unit = CoZeroW id :.: ZeroW id
  counit (ZeroW h :.: CoZeroW i) = i . h
