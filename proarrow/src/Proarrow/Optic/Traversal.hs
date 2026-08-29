{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Optic.Traversal where

import GHC.Generics qualified as G
import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Tensor)
import Proarrow.Category.Monoidal.Action (CoprodAction)
import Proarrow.Category.Monoidal.Distributive
  ( Bicartesian
  , Cotraversable (..)
  , Distributive
  , StrongDistributiveProfunctor
  , Traversable (..)
  , corepTraverse
  , repTraverse
  )
import Proarrow.Category.Monoidal.Strength (Strong (..), strongId)
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Coprod (..)
  , Coproduct
  , HasBinaryCoproducts (..)
  , HasCoproducts
  , nil
  , (++)
  )
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, (\\), type (+->))
import Proarrow.Limit.BinaryProduct (Cartesian, HasBinaryProducts (..), Product)
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( CompactFlavor (..)
  , ExOptic (..)
  , FLAVOR
  , IsOptic (..)
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , SubFlavor (..)
  , convert
  , withLegs
  )
import Proarrow.Optic.Fold (FoldRes (..))
import Proarrow.Optic.Setter (SetterRes (..))
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..), coindex)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), RepCostar (..), Representable (..))
import Prelude (Either (..), const, either, uncurry, ($))

type TravRes :: forall {k}. FLAVOR k k
class (SetterRes p q, FoldRes p q) => TravRes (p :: k +-> k) (q :: k +-> k) where
  travP :: (StrongDistributiveProfunctor r, Cartesian k) => p s a -> q b t -> r a b -> r s t
instance (Traversable t, Representable t) => TravRes t (RepCostar t) where
  travP l (RepCostar r) = dimap (index l) r . repTraverse @t

-- | The former cotraversal witness: a corepresentable 'Cotraversable' functor builds @s@ from a
-- shape of @a@'s. Its 'travP' distributes an SDP exactly as the old @cotravP@ did -- for these
-- (representable) witnesses a cotraversal /is/ a traversal, which is why there is no separate
-- 'Cotraversal' optic.
instance (Cotraversable t, Corepresentable t) => TravRes (CorepStar t) t where
  travP (CorepStar l) co = dimap l (coindex co) . corepTraverse @t

instance (HasBinaryProducts k, Ob (s :: k)) => TravRes (Rep (Product s)) (Corep (Product s)) where
  travP (Rep p) (Corep q) r = dimap p q (act @Tensor @_ @s r)
instance (HasCoproducts k, Ob t) => TravRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  travP (Rep p) (Corep q) r = dimap p q (act @CoprodAction @_ @(COPR t) r)
instance (CategoryOf k) => TravRes (Id :: k +-> k) (Id :: k +-> k) where
  travP (Id l) (Id r) = dimap l r
instance (TravRes f g, TravRes f' g') => TravRes (f :.: f') (g' :.: g) where
  travP (f :.: f') (g' :.: g) = travP @f @g f g . travP @f' @g' f' g'

instance CompactFlavor TravRes

instance SubFlavor TravRes SetterRes where subFlavor r = r
instance SubFlavor TravRes FoldRes where subFlavor r = r

type Traversal (s :: k) (t :: k) a b = Optic (Prostrong TravRes) s t a b
type Traversal' s a = Traversal s s a a

-- | Traverse: distribute any 'StrongDistributiveProfunctor' -- not merely a @Star f@ (the
-- Hask van-Laarhoven shape) -- through any optic that is at least a 'Traversal'. Works for an
-- arbitrary profunctor carrier by handing it to 'travP', rather than relying on a per-carrier
-- @'Prostrong' w p@ bridge (which could only ever cover specific carrier heads).
traverseOf
  :: forall {k} w (s :: k) (t :: k) a b p
   . (Distributive k, Cartesian k, StrongDistributiveProfunctor p, SubFlavor w TravRes)
  => Optic (Prostrong w) s t a b -> p a b -> p s t
traverseOf o pab = withLegs (\l r -> travP l r pab) (convert @(Prostrong w) @TravRes o)

instance IsOptic StrongDistributiveProfunctor where withProfunctor r = r

-- | A traversal in the profunctor-class-flavored encoding (cf. 'Proarrow.Optic.PIso'), used by
-- the "GHC.Generics" combinators below. Equivalent to 'Traversal' via 'toPTraversal' and
-- 'fromPTraversal'.
type PTraversal s t a b = Optic StrongDistributiveProfunctor s t a b

-- | Half of the equivalence between the two traversal encodings: eliminate the existential
-- witnesses with 'travP' at the caller's profunctor.
toPTraversal
  :: forall {k} (s :: k) (t :: k) a b
   . (Distributive k, Cartesian k)
  => Traversal s t a b -> PTraversal s t a b
toPTraversal = withLegs \l@Objs r@Objs -> Optic (travP l r)

v1Optic :: PTraversal (G.V1 a) (G.V1 a') a a'
v1Optic = Optic \_ -> dimap (\case {}) (\case {}) nil

u1Optic :: PTraversal (G.U1 a) (G.U1 a') a a'
u1Optic = Optic \_ -> dimap (const ()) (\() -> G.U1) one

par1Optic :: PTraversal (G.Par1 a) (G.Par1 a') a a'
par1Optic = Optic (dimap G.unPar1 G.Par1)

rec1Optic :: PTraversal (f a) (f a') a a' -> PTraversal (G.Rec1 f a) (G.Rec1 f a') a a'
rec1Optic (Optic l) = Optic \p -> dimap G.unRec1 G.Rec1 (l p)

m1Optic :: PTraversal (f a) (f a') a a' -> PTraversal (G.M1 i k f a) (G.M1 i k f a') a a'
m1Optic (Optic l) = Optic \p -> dimap G.unM1 G.M1 (l p)

k1Optic :: forall i k a a'. PTraversal (G.K1 i k a) (G.K1 i k a') a a'
k1Optic = Optic \_ -> dimap G.unK1 G.K1 strongId

plusOptic
  :: PTraversal (p a) (p a') a a'
  -> PTraversal (q a) (q a') a a'
  -> PTraversal ((p G.:+: q) a) ((p G.:+: q) a') a a'
plusOptic (Optic l) (Optic r) = Optic \p -> dimap (\case G.L1 f -> Left f; G.R1 f -> Right f) (either G.L1 G.R1) (l p ++ r p)

multOptic
  :: PTraversal (p a) (p a') a a'
  -> PTraversal (q a) (q a') a a'
  -> PTraversal ((p G.:*: q) a) ((p G.:*: q) a') a a'
multOptic (Optic l) (Optic r) = Optic \p -> dimap (\(f G.:*: g) -> (f, g)) (uncurry (G.:*:)) (l p ** r p)

compOptic
  :: PTraversal (p (q a)) (p (q a')) (q a) (q a')
  -> PTraversal (q a) (q a') a a'
  -> PTraversal ((p G.:.: q) a) ((p G.:.: q) a') a a'
compOptic (Optic l) (Optic r) = Optic \p -> dimap G.unComp1 G.Comp1 (l (r p))

-- * The free traversal profunctor

-- | Witness pair for traversing two juxtaposed (tensored) parts in sequence, both parts
-- focusing the same type @x@.
--
-- 'Beside' and 'CoBeside' are each one half of 'Proarrow.Profunctor.Instance.Day.Day' with the
-- two foci types identified -- a one-sided Day convolution, pointwise in the shared focus. The
-- identification is essential: a @('Proarrow.Profunctor.Instance.Day.Day' p1 p2,
-- 'Proarrow.Profunctor.Instance.Day.Day' q1 q2)@ witness pair admits no componentwise 'travP'
-- (that would require splitting a 'StrongDistributiveProfunctor' value at a tensor), which is
-- why 'Proarrow.Optic.Day.DayRes'-flavored optics focus /pairs/ @a1 ** a2@ while these
-- witnesses visit each half's foci in sequence.
type Beside :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
data Beside p1 p2 s x where
  Beside :: (s ~> (s1 ** s2)) -> p1 s1 x -> p2 s2 x -> Beside p1 p2 s x

type CoBeside :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
data CoBeside q1 q2 x t where
  CoBeside :: q1 x t1 -> q2 x t2 -> ((t1 ** t2) ~> t) -> CoBeside q1 q2 x t

instance (Profunctor p1, Profunctor p2, Monoidal k) => Profunctor (Beside p1 p2 :: k +-> k) where
  dimap l r (Beside d x y) = Beside (d . l) (rmap r x) (rmap r y) \\ l
  r \\ Beside d x _ = r \\ d \\ x
instance (Profunctor q1, Profunctor q2, Monoidal k) => Profunctor (CoBeside q1 q2 :: k +-> k) where
  dimap l r (CoBeside u v c) = CoBeside (lmap l u) (lmap l v) (r . c) \\ r
  r \\ CoBeside u _ c = r \\ u \\ c

instance (SetterRes p1 q1, SetterRes p2 q2, Monoidal k) => SetterRes (Beside p1 p2 :: k +-> k) (CoBeside q1 q2) where
  overP (Beside d l1 l2) (CoBeside r1 r2 c) f = c . (overP @p1 @q1 l1 r1 f ** overP @p2 @q2 l2 r2 f) . d
instance (FoldRes p1 q1, FoldRes p2 q2, Monoidal k) => FoldRes (Beside p1 p2 :: k +-> k) (CoBeside q1 q2 :: k +-> k) where
  foldMapP (Beside d l1 l2) am = mappend . (foldMapP @p1 @q1 l1 am ** foldMapP @p2 @q2 l2 am) . d
instance (TravRes p1 q1, TravRes p2 q2, Monoidal k) => TravRes (Beside p1 p2 :: k +-> k) (CoBeside q1 q2) where
  travP (Beside d l1 l2) (CoBeside r1 r2 c) r = dimap d c (travP @p1 @q1 l1 r1 r ** travP @p2 @q2 l2 r2 r)
instance (Proadjunction p1 q1, Proadjunction p2 q2, Monoidal k) => Proadjunction (Beside p1 p2 :: k +-> k) (CoBeside q1 q2) where
  unit @a = case unit @p1 @q1 @a of
    (:.:) @m1 u1 v1 -> case unit @p2 @q2 @a of
      (:.:) @m2 u2 v2 -> withOb2 @k @m1 @m2 (CoBeside u1 u2 id :.: Beside id v1 v2) \\ v1 \\ v2
  counit (Beside d l1 l2 :.: CoBeside r1 r2 c) = c . (counit (l1 :.: r1) ** counit (l2 :.: r2)) . d

-- | Witness pair for traversing one of two alternative (coproduct) parts: the same one-sided
-- Day convolution as 'Beside'\/'CoBeside', but over the coproduct monoidal structure (cf.
-- 'Coprod').
type BesideSum :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
data BesideSum p1 p2 s x where
  BesideSum :: (s ~> (s1 || s2)) -> p1 s1 x -> p2 s2 x -> BesideSum p1 p2 s x

type CoBesideSum :: forall {k}. (k +-> k) -> (k +-> k) -> k +-> k
data CoBesideSum q1 q2 x t where
  CoBesideSum :: q1 x t1 -> q2 x t2 -> ((t1 || t2) ~> t) -> CoBesideSum q1 q2 x t

instance (Profunctor p1, Profunctor p2, CategoryOf k) => Profunctor (BesideSum p1 p2 :: k +-> k) where
  dimap l r (BesideSum d x y) = BesideSum (d . l) (rmap r x) (rmap r y) \\ l
  r \\ BesideSum d x _ = r \\ d \\ x
instance (Profunctor q1, Profunctor q2, CategoryOf k) => Profunctor (CoBesideSum q1 q2 :: k +-> k) where
  dimap l r (CoBesideSum u v c) = CoBesideSum (lmap l u) (lmap l v) (r . c) \\ r
  r \\ CoBesideSum u _ c = r \\ u \\ c

instance (SetterRes p1 q1, SetterRes p2 q2, HasBinaryCoproducts k) => SetterRes (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2) where
  overP (BesideSum d l1 l2) (CoBesideSum r1 r2 c) f = c . (overP @p1 @q1 l1 r1 f +++ overP @p2 @q2 l2 r2 f) . d
instance
  (FoldRes p1 q1, FoldRes p2 q2, HasBinaryCoproducts k)
  => FoldRes (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2 :: k +-> k)
  where
  foldMapP (BesideSum d l1 l2) am = (foldMapP @p1 @q1 l1 am ||| foldMapP @p2 @q2 l2 am) . d
instance (TravRes p1 q1, TravRes p2 q2, HasBinaryCoproducts k) => TravRes (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2) where
  travP (BesideSum d l1 l2) (CoBesideSum r1 r2 c) r = dimap d c (travP @p1 @q1 l1 r1 r ++ travP @p2 @q2 l2 r2 r)
instance
  (Proadjunction p1 q1, Proadjunction p2 q2, HasBinaryCoproducts k)
  => Proadjunction (BesideSum p1 p2 :: k +-> k) (CoBesideSum q1 q2)
  where
  unit @a = case unit @p1 @q1 @a of
    (:.:) @m1 u1 v1 -> case unit @p2 @q2 @a of
      (:.:) @m2 u2 v2 -> withObCoprod @k @m1 @m2 (CoBesideSum u1 u2 id :.: BesideSum id v1 v2) \\ v1 \\ v2
  counit (BesideSum d l1 l2 :.: CoBesideSum r1 r2 c) = c . (counit (l1 :.: r1) +++ counit (l2 :.: r2)) . d

-- | Witness pair with no foci at all: decompose to 'Unit' and rebuild.
--
-- 'UnitW' and 'CoUnitW' are the two halves of 'Proarrow.Profunctor.Instance.Day.DayUnit', one
-- per side of the witness pair, with a phantom focus: together with 'Beside'\/'CoBeside' being
-- the halves of 'Proarrow.Profunctor.Instance.Day.Day', the witness pairs here are exactly the
-- Day-monoidal structure on profunctors (@'Proarrow.Category.Monoidal.Monoidal' (j '+->' k)@),
-- split at the focus. The split is forced: a whole 'Proarrow.Profunctor.Instance.Day.DayUnit'
-- on the decomposition side would demand @Unit ~> a@ for an arbitrary focus @a@.
type UnitW :: forall {k}. k +-> k
data UnitW s x where
  UnitW :: (Ob x) => (s ~> Unit) -> UnitW s x

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
instance (Monoidal k) => TravRes (UnitW :: k +-> k) CoUnitW where
  travP (UnitW h) (CoUnitW i) _ = dimap h i one
instance (Monoidal k) => Proadjunction (UnitW :: k +-> k) CoUnitW where
  unit = CoUnitW id :.: UnitW id
  counit (UnitW h :.: CoUnitW i) = i . h

-- | Witness pair for the impossible case: decompose to the initial object -- the halves of the
-- (unspelled) unit of Day convolution over the coproduct monoidal structure, cf.
-- 'UnitW'\/'CoUnitW'.
type ZeroW :: forall {k}. k +-> k
data ZeroW s x where
  ZeroW :: (Ob x) => (s ~> InitialObject) -> ZeroW s x

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
instance (HasInitialObject k) => TravRes (ZeroW :: k +-> k) CoZeroW where
  travP (ZeroW h) (CoZeroW i) _ = dimap h i nil
instance (HasInitialObject k) => Proadjunction (ZeroW :: k +-> k) CoZeroW where
  unit = CoZeroW id :.: ZeroW id
  counit (ZeroW h :.: CoZeroW i) = i . h

besideTensor
  :: forall {k} (a :: k) b s1 t1 s2 t2
   . (Bicartesian k, Ob a, Ob b)
  => ExOptic TravRes a b s1 t1 -> ExOptic TravRes a b s2 t2 -> ExOptic TravRes a b (s1 ** s2) (t1 ** t2)
besideTensor l r =
  compress l \p1@Objs q1@Objs ->
    compress r \p2@Objs q2@Objs ->
      withOb2 @k @s1 @s2 $
        withOb2 @k @t1 @t2 $
          ExProstrong (Beside id p1 p2 :.: ExIso id id :.: CoBeside q1 q2 id)

besideSum
  :: forall {k} (a :: k) b s1 t1 s2 t2
   . (Bicartesian k, Ob a, Ob b)
  => ExOptic TravRes a b s1 t1 -> ExOptic TravRes a b s2 t2 -> ExOptic TravRes a b (s1 || s2) (t1 || t2)
besideSum l r =
  compress l \p1@Objs q1@Objs ->
    compress r \p2@Objs q2@Objs ->
      withObCoprod @k @s1 @s2 $
        withObCoprod @k @t1 @t2 $
          ExProstrong (BesideSum id p1 p2 :.: ExIso id id :.: CoBesideSum q1 q2 id)

-- | The free 'TravRes'-strong profunctor is itself a 'StrongDistributiveProfunctor': together
-- with the instances below, this is the theorem making 'fromPTraversal' possible.
instance (Bicartesian k, Ob (a :: k), Ob b) => MonoidalProfunctor (ExOptic TravRes a b :: k +-> k) where
  one = ExProstrong (UnitW id :.: ExIso id id :.: CoUnitW id)
  l ** r = besideTensor l r

instance (Bicartesian k, Ob (a :: k), Ob b) => MonoidalProfunctor (Coprod (ExOptic TravRes a b :: k +-> k)) where
  one = Coprod (ExProstrong (ZeroW id :.: ExIso id id :.: CoZeroW id))
  Coprod l ** Coprod r = Coprod (besideSum l r)

instance (Bicartesian k, Ob (a :: k), Ob b) => Strong Tensor (ExOptic TravRes a b :: k +-> k) where
  act @x @y @z e@Objs =
    withOb2 @k @x @y $
      withOb2 @k @x @z $
        withObProd @k @x @y $
          withObProd @k @x @z $
            ExProstrong @(Rep (Product x)) @(Corep (Product x)) (Rep id :.: e :.: Corep id)

instance (Bicartesian k, Ob (a :: k), Ob b) => Strong CoprodAction (ExOptic TravRes a b :: k +-> k) where
  act @cx @y @z e@Objs =
    withObCoprod @k @(UN COPR cx) @y $
      withObCoprod @k @(UN COPR cx) @z $
        ExProstrong @(Rep (Coproduct (UN COPR cx))) @(Corep (Coproduct (UN COPR cx))) (Rep id :.: e :.: Corep id)

-- | The other half of the equivalence between the encodings: instantiate the
-- profunctor-class-flavored traversal at the free 'TravRes'-strong profunctor.
fromPTraversal
  :: forall {k} (s :: k) (t :: k) a b
   . (Bicartesian k)
  => PTraversal s t a b -> Traversal s t a b
fromPTraversal = convert
