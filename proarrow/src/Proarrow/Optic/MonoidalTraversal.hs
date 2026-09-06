{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __monoidal traversal__ optic and its free-profunctor apparatus, split out of
-- "Proarrow.Optic.Traversal" (which keeps the mutually-recursive 'TravRes'\/'MonTravRes' flavor
-- classes and their leaf instances). A 'MonoidalTraversal' distributes any
-- 'StrongDistributiveProfunctor' with no product-strength requirement; the profunctor-class
-- encoding 'PTraversal' converts to and from it via 'toPTraversal'\/'fromPTraversal', the latter
-- through the free 'MonTravRes'-strong profunctor @'ExOptic' 'MonTravRes'@ (an SDP, via the
-- tensor-strength witness 'TensorW').
module Proarrow.Optic.MonoidalTraversal where

import GHC.Generics qualified as G
import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, Tensor)
import Proarrow.Category.Monoidal.Action (CoprodAction)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Distributive (Distributive, StrongDistributiveProfunctor)
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
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, obj, (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( CompactFlavor (..)
  , ExOptic (..)
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
import Proarrow.Optic.Traversal
  ( Beside (..)
  , BesideSum (..)
  , CoBeside (..)
  , CoBesideSum (..)
  , CoUnitW (..)
  , CoZeroW (..)
  , MonTravRes (..)
  , TravRes (..)
  , UnitW (..)
  , ZeroW (..)
  )
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Rep (..))
import Prelude (Either (..), const, either, uncurry, ($))

type MonoidalTraversal (s :: k) (t :: k) a b = Optic (Prostrong MonTravRes) s t a b

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
instance (CopyDiscard k, Ob (a :: k)) => FoldRes (TensorW a :: k +-> k) (CoTensorW a) where
  foldMapP (TensorW h) am = leftUnitor . (discard @k @a ** am) . h
instance (CopyDiscard k, Ob (a :: k)) => TravRes (TensorW a :: k +-> k) (CoTensorW a)
instance (CopyDiscard k, Ob (a :: k)) => MonTravRes (TensorW a :: k +-> k) (CoTensorW a) where
  monTravP (TensorW h) (CoTensorW i) r = dimap h i (act @Tensor @_ @a r)

besideTensor
  :: forall {k} (a :: k) b s1 t1 s2 t2
   . (Monoidal k, Ob a, Ob b)
  => ExOptic MonTravRes a b s1 t1 -> ExOptic MonTravRes a b s2 t2 -> ExOptic MonTravRes a b (s1 ** s2) (t1 ** t2)
besideTensor l r =
  compress l \p1@Objs q1@Objs ->
    compress r \p2@Objs q2@Objs ->
      withOb2 @k @s1 @s2 $
        withOb2 @k @t1 @t2 $
          ExProstrong (Beside id p1 p2 :.: ExIso id id :.: CoBeside q1 q2 id)

besideSum
  :: forall {k} (a :: k) b s1 t1 s2 t2
   . (HasBinaryCoproducts k, Ob a, Ob b)
  => ExOptic MonTravRes a b s1 t1 -> ExOptic MonTravRes a b s2 t2 -> ExOptic MonTravRes a b (s1 || s2) (t1 || t2)
besideSum l r =
  compress l \p1@Objs q1@Objs ->
    compress r \p2@Objs q2@Objs ->
      withObCoprod @k @s1 @s2 $
        withObCoprod @k @t1 @t2 $
          ExProstrong (BesideSum id p1 p2 :.: ExIso id id :.: CoBesideSum q1 q2 id)

instance (Monoidal k, Ob (a :: k), Ob b) => MonoidalProfunctor (ExOptic MonTravRes a b :: k +-> k) where
  one = ExProstrong (UnitW id :.: ExIso id id :.: CoUnitW id)
  l ** r = besideTensor l r

instance (HasCoproducts k, Ob (a :: k), Ob b) => MonoidalProfunctor (Coprod (ExOptic MonTravRes a b :: k +-> k)) where
  one = Coprod (ExProstrong (ZeroW id :.: ExIso id id :.: CoZeroW id))
  Coprod l ** Coprod r = Coprod (besideSum l r)

instance (CopyDiscard k, Ob (a :: k), Ob b) => Strong Tensor (ExOptic MonTravRes a b :: k +-> k) where
  act @x @y @z e@Objs =
    withOb2 @k @x @y $
      withOb2 @k @x @z $
        ExProstrong @(TensorW x) @(CoTensorW x) (TensorW id :.: e :.: CoTensorW id)

instance (HasCoproducts k, CopyDiscard k, Ob (a :: k), Ob b) => Strong CoprodAction (ExOptic MonTravRes a b :: k +-> k) where
  act @cx @y @z e@Objs =
    withObCoprod @k @(UN COPR cx) @y $
      withObCoprod @k @(UN COPR cx) @z $
        ExProstrong @(Rep (Coproduct (UN COPR cx))) @(Corep (Coproduct (UN COPR cx))) (Rep id :.: e :.: Corep id)

-- | The other half of the equivalence between the encodings: instantiate the
-- profunctor-class-flavored traversal at the free __monoidal-traversal__ profunctor
-- @'ExOptic' 'MonTravRes'@. Because that carrier's 'Proarrow.Category.Monoidal.Strength.MonStrong'
-- instance uses the tensor-strength witness 'TensorW' (not a product lens), this needs no
-- 'Proarrow.Limit.BinaryProduct.Cartesian' (@tensor = product@), only 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' (a discard @a '~>' 'Unit' for the residual) -- which is
-- exactly what the coproduct-prism side (@'Strong' 'CoprodAction' ('ExOptic' 'MonTravRes')@) already
-- demanded, so no constraint is added beyond relaxing 'Cartesian' to 'CopyDiscard' -- enabling e.g.
-- the biproduct categories @Mat@ and @FinRel@ (but not @LINEAR@, which cannot discard). A 'Traversal'
-- is recovered for free wherever one is needed, since @'MonTravRes'@ is a 'SubFlavor' of 'TravRes'.
fromPTraversal
  :: forall {k} (s :: k) (t :: k) a b
   . (Distributive k, CopyDiscard k, SymMonoidal k)
  => PTraversal s t a b -> MonoidalTraversal s t a b
fromPTraversal = convert

-- | Like 'traverseOf', but for a 'MonoidalTraversal' -- distributes any 'StrongDistributiveProfunctor'
-- with /no/ product-strength requirement on the carrier. Every non-lens traversal (prism,
-- 'Traversable' functor, ...) is a monoidal traversal, so this accepts carriers like @'Writer' w@
-- that are tensor-strong but not product-strong.
monTraverseOf
  :: forall {k} w (s :: k) (t :: k) a b p
   . (Distributive k, StrongDistributiveProfunctor p, SubFlavor w MonTravRes)
  => Optic (Prostrong w) s t a b -> p a b -> p s t
monTraverseOf o pab = withLegs (\l r -> monTravP l r pab) (convert @(Prostrong w) @MonTravRes o)

instance IsOptic StrongDistributiveProfunctor where withProfunctor r = r

-- | A traversal in the profunctor-class-flavored encoding (cf. 'Proarrow.Optic.PIso'), used by
-- the "GHC.Generics" combinators below. Equivalent to 'Traversal' via 'toPTraversal' and
-- 'fromPTraversal'.
type PTraversal s t a b = Optic StrongDistributiveProfunctor s t a b

-- | Half of the equivalence between the two traversal encodings: eliminate the existential
-- witnesses with 'travP' at the caller's profunctor.
toPTraversal
  :: forall {k} (s :: k) (t :: k) a b
   . (Distributive k)
  => MonoidalTraversal s t a b -> PTraversal s t a b
toPTraversal = withLegs \l@Objs r@Objs -> Optic (monTravP l r)

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
