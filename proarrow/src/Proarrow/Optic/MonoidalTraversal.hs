{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __monoidal traversal__ optic and its free-profunctor apparatus, split out of
-- "Proarrow.Optic.Traversal" (which keeps the mutually-recursive 'TravFl'\/'MonTravFl' flavor
-- classes and their leaf instances). A 'MonoidalTraversal' distributes any
-- 'StrongDistributiveProfunctor' with no product-strength requirement; the profunctor-class
-- encoding 'PTraversal' converts to and from it via 'toPTraversal'\/'fromPTraversal', the latter
-- through the generic carrier @'ExOptic' 'MonTravFl'@, made an SDP here by generators (the Day
-- halves, the tensor-action witness @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' _)@ and the coproduct prism).
module Proarrow.Optic.MonoidalTraversal where

import GHC.Generics qualified as G
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt, CoprodAction, ProdAction)
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
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD (..), Product)
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic (..)
  , FLAVOR
  , Flavor
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , convert
  , withLegs
  , type (:&&:)
  )
import Proarrow.Optic.Traversal
  ( Beside
  , BesideSum
  , CoBeside
  , CoBesideSum
  , CoUnitW (..)
  , CoZeroW (..)
  , MonTravFl (..)
  , TravFl (..)
  , Traversal
  , UnitW (..)
  , ZeroW (..)
  )
import Proarrow.Profunctor.Corepresentable (Corep, Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Rep, Representable (..))
import Prelude (Either (..), const, either, uncurry, ($))

type MonoidalTraversal (s :: k) (t :: k) a b = Optic (Prostrong MonTravFl) s t a b
type MonoidalTraversal' s a = MonoidalTraversal s s a a

-- * The generic carrier is a strong distributive profunctor, by generators

-- Every piece of 'StrongDistributiveProfunctor' structure on the generic carrier @'ExOptic' w a b@ is
-- "compose one more generating witness pair onto the legs", so each instance below holds for
-- /any/ closed flavor @w@ that contains the relevant generator: the Day halves 'UnitW'\/'Beside'
-- for the tensor, 'ZeroW'\/'BesideSum' for the coproduct, the tensor-action pair for tensor strength and the
-- coproduct\/product prism and lens witnesses for the two action strengths. This is what lets a
-- profunctor-class-flavored optic ('PTraversal', 'PTraversalFull') be eliminated through 'ExOptic'
-- by the encoding-agnostic eliminators ('Proarrow.Optic.Setter.over', 'Proarrow.Optic.Fold.foldMapOf', ...),
-- and what 'fromPTraversal' \/ 'traversal' instantiate at.

exBeside
  :: forall {k} (w :: FLAVOR k k) (a :: k) b s1 t1 s2 t2
   . ( Monoidal k
     , forall p1 p2 q1 q2
        . (w p1 q1, w p2 q2, Profunctor p1, Profunctor p2, Profunctor q1, Profunctor q2)
       => w (Beside p1 p2) (CoBeside q1 q2)
     )
  => ExOptic w a b s1 t1 -> ExOptic w a b s2 t2 -> ExOptic w a b (s1 ** s2) (t1 ** t2)
exBeside (ExOptic @p1 @q1 l1@Objs r1@Objs) (ExOptic @p2 @q2 l2@Objs r2@Objs) =
  withOb2 @k @s1 @s2 $
    withOb2 @k @t1 @t2 $
      ExOptic @(Beside p1 p2) @(CoBeside q1 q2)
        (repUniv :.: (l1 :**: l2) :.: repUniv)
        (corepUniv :.: (r1 :**: r2) :.: corepUniv)

exBesideSum
  :: forall {k} (w :: FLAVOR k k) (a :: k) b s1 t1 s2 t2
   . ( HasBinaryCoproducts k
     , forall p1 p2 q1 q2
        . (w p1 q1, w p2 q2, Profunctor p1, Profunctor p2, Profunctor q1, Profunctor q2)
       => w (BesideSum p1 p2) (CoBesideSum q1 q2)
     )
  => ExOptic w a b s1 t1 -> ExOptic w a b s2 t2 -> ExOptic w a b (s1 || s2) (t1 || t2)
exBesideSum (ExOptic @p1 @q1 l1@Objs r1@Objs) (ExOptic @p2 @q2 l2@Objs r2@Objs) =
  withObCoprod @k @s1 @s2 $
    withObCoprod @k @t1 @t2 $
      ExOptic @(BesideSum p1 p2) @(CoBesideSum q1 q2)
        (repUniv :.: (l1 :**: l2) :.: repUniv)
        (corepUniv :.: (r1 :**: r2) :.: corepUniv)

instance
  ( Monoidal k
  , Ob (a :: k)
  , Ob b
  , w UnitW CoUnitW
  , forall p1 p2 q1 q2
     . (w p1 q1, w p2 q2, Profunctor p1, Profunctor p2, Profunctor q1, Profunctor q2)
    => w (Beside p1 p2) (CoBeside q1 q2)
  )
  => MonoidalProfunctor (ExOptic w a b :: k +-> k)
  where
  one = ExOptic (UnitW id) (CoUnitW id)
  (**) = exBeside

instance
  ( HasCoproducts k
  , Ob (a :: k)
  , Ob b
  , w ZeroW CoZeroW
  , forall p1 p2 q1 q2
     . (w p1 q1, w p2 q2, Profunctor p1, Profunctor p2, Profunctor q1, Profunctor q2)
    => w (BesideSum p1 p2) (CoBesideSum q1 q2)
  )
  => MonoidalProfunctor (Coprod (ExOptic w a b :: k +-> k))
  where
  one = Coprod (ExOptic (ZeroW id) (CoZeroW id))
  Coprod l ** Coprod r = Coprod (exBesideSum l r)

instance
  ( Monoidal k
  , Ob (a :: k)
  , Ob b
  , Flavor w
  , forall (x :: k). (Ob x) => w (Rep (ActionAt Tensor x)) (Corep (ActionAt Tensor x))
  )
  => Strong Tensor (ExOptic w a b :: k +-> k)
  where
  act @x @y @z (ExOptic @p @q l@Objs r@Objs) =
    withOb2 @k @x @y $
      withOb2 @k @x @z $
        ExOptic @(Rep (ActionAt Tensor x) :.: p) @(q :.: Corep (ActionAt Tensor x)) (repUniv :.: l) (r :.: corepUniv)

instance
  ( HasCoproducts k
  , Ob (a :: k)
  , Ob b
  , Flavor w
  , forall (t :: k). (Ob t) => w (Rep (Coproduct t)) (Corep (Coproduct t))
  )
  => Strong CoprodAction (ExOptic w a b :: k +-> k)
  where
  act @cx @y @z (ExOptic @p @q l@Objs r@Objs) =
    withObCoprod @k @(UN COPR cx) @y $
      withObCoprod @k @(UN COPR cx) @z $
        ExOptic @(Rep (Coproduct (UN COPR cx)) :.: p) @(q :.: Corep (Coproduct (UN COPR cx))) (repUniv :.: l) (r :.: corepUniv)

instance
  (HasProducts k, Ob (a :: k), Ob b, Flavor w, forall (s :: k). (Ob s) => w (Rep (Product s)) (Corep (Product s)))
  => Strong ProdAction (ExOptic w a b :: k +-> k)
  where
  act @px @y @z (ExOptic @p @q l@Objs r@Objs) =
    withObProd @k @(UN PR px) @y $
      withObProd @k @(UN PR px) @z $
        ExOptic @(Rep (Product (UN PR px)) :.: p) @(q :.: Corep (Product (UN PR px))) (repUniv :.: l) (r :.: corepUniv)

-- | The other half of the equivalence between the encodings: instantiate the
-- profunctor-class-flavored traversal at the generic carrier @'ExOptic' 'MonTravFl' a b@, which is
-- an SDP by the by-generator instances above. Because its tensor strength comes from the
-- tensor-action witness @'Rep' ('ActionAt' 'Tensor' _)@ (not a product lens), this needs no
-- 'Proarrow.Limit.BinaryProduct.Cartesian' (@tensor = product@), only 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' (a discard @a '~>' 'Unit' for the residual) -- which is
-- exactly what the coproduct-prism witness already demanded -- enabling e.g. the biproduct
-- categories @Mat@ and @FinRel@ (but not @LINEAR@, which cannot discard). A 'Traversal' is
-- recovered for free wherever one is needed, since @'MonTravFl'@ is a 'SubFlavor' of 'TravFl'.
fromPTraversal
  :: forall {k} (s :: k) (t :: k) a b
   . (Distributive k, CopyDiscard k, SymMonoidal k)
  => PTraversal s t a b -> MonoidalTraversal s t a b
fromPTraversal = convert

-- | Like 'Proarrow.Optic.Traversal.traverseOf', but for a 'MonoidalTraversal' -- distributes any 'StrongDistributiveProfunctor'
-- with /no/ product-strength requirement on the carrier. Every non-lens traversal (prism,
-- 'Proarrow.Category.Monoidal.Distributive.Traversable' functor, ...) is a monoidal traversal, so this accepts carriers like @'Proarrow.Promonad.Writer.Writer' w@
-- that are tensor-strong but not product-strong.
--
-- Accepts any encoding (cf. 'Proarrow.Optic.Traversal.traverseOf'): a 'PTraversal' works directly,
-- as does a '(%)'-composite.
monTraverseOf
  :: forall {k} c (s :: k) (t :: k) a b p
   . (Distributive k, StrongDistributiveProfunctor p, (Ob a, Ob b) => c (ExOptic MonTravFl a b))
  => Optic c s t a b -> p a b -> p s t
monTraverseOf o pab = withLegs @MonTravFl o \l r -> monTravP l r pab

-- | A traversal in the profunctor-class-flavored encoding (cf. 'Proarrow.Optic.PIso'), used by
-- the "GHC.Generics" combinators below. Equivalent to 'Traversal' via 'toPTraversal' and
-- 'fromPTraversal'.
type PTraversal s t a b = Optic StrongDistributiveProfunctor s t a b

type PTraversal' s a = PTraversal s s a a

-- | Half of the equivalence between the two traversal encodings: eliminate the existential
-- witnesses with 'travP' at the caller's profunctor.
toPTraversal
  :: forall {k} (s :: k) (t :: k) a b
   . (Distributive k)
  => MonoidalTraversal s t a b -> PTraversal s t a b
toPTraversal o = withLegs @MonTravFl o \l@Objs r@Objs -> Optic (monTravP l r)

-- | A full traversal in the profunctor-class encoding: distributes any profunctor carrying both
-- distributive strength and __product__ strength -- exactly the constraint 'travP' demands. This is
-- the 'Traversal' analog of 'PTraversal', which drops the product strength (all it needs for a
-- 'MonoidalTraversal'). Equivalent to 'Traversal' via 'toPTraversalFull' and 'traversal'.
type PTraversalFull s t a b = Optic (StrongDistributiveProfunctor :&&: Strong ProdAction) s t a b

-- | Build a 'Traversal' from its van-Laarhoven \/ profunctor-class form, by instantiating the
-- rank-2 function at the generic carrier @'ExOptic' 'TravFl' a b@ (a 'StrongDistributiveProfunctor'
-- /and/ @'Strong' 'ProdAction'@, unlike @'ExOptic' 'MonTravFl' a b@, since 'TravFl' contains the
-- product-lens witness). The 'Traversal' analog of 'fromPTraversal'.
traversal
  :: forall {k} (s :: k) t a b
   . (Distributive k, CopyDiscard k, SymMonoidal k, HasProducts k, Ob a, Ob b, Ob s, Ob t)
  => (forall r. (StrongDistributiveProfunctor r, Strong ProdAction r) => r a b -> r s t) -> Traversal s t a b
traversal f = convert (Optic f :: PTraversalFull s t a b)

-- | Eliminate a 'Traversal' to its profunctor-class form (the analog of 'toPTraversal'): run 'travP'
-- at the caller's profunctor.
toPTraversalFull
  :: forall {k} (s :: k) (t :: k) a b
   . (Distributive k)
  => Traversal s t a b -> PTraversalFull s t a b
toPTraversalFull o = withLegs @TravFl o \l@Objs r@Objs -> Optic (travP l r)

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
