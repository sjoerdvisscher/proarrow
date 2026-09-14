{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __monoidal lens__: the coend optic for the tensor action with a __comonoidal residual__,
--
-- > MonoidalLens s t a b = exists m. Comonoid m => (s ~> m ** a, m ** b ~> t)
--
-- The residual @m@ is carried through the tensor, and being a 'Comonoid' it can be /discarded/
-- (@'counit' :: m ~> 'Unit'@) and /copied/ -- which is exactly what a lens's @get@ needs. So a
-- monoidal lens is a genuine lens (it views, sets, folds and traverses), and it sits below
-- 'Proarrow.Optic.MonoidalTraversal.MonoidalTraversal' and 'Proarrow.Optic.Getter.Getter' in the
-- lattice, mirroring the ordinary 'Proarrow.Optic.Lens.Lens' below
-- 'Proarrow.Optic.AffineTraversal.AffineTraversal':
--
-- > Lens         <: { Getter, AffineTraversal, Glass }                     -- product residual
-- > MonoidalLens <: { Getter, MonoidalTraversal, AffineTraversal, Glass }  -- comonoidal tensor residual
--
-- It is not a 'Proarrow.Optic.Lens.Lens', because 'Proarrow.Optic.Lens.putP' promises to work with
-- binary products alone, where the tensor and the product are unrelated. It /is/ an
-- 'Proarrow.Optic.AffineTraversal.AffineTraversal' and a 'Proarrow.Optic.Glass.Glass', because
-- their methods ask for a cartesian category, in which the tensor is the product and the residual
-- can be projected out.
module Proarrow.Optic.MonoidalLens where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal, Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Colimit.BinaryCoproduct (lft, rgt)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), first)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid, ComonoidOn, comonoidOn, tensorComonoid, unitComonoid)
import Proarrow.Monoid qualified as Mon
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Optic
  , Prostrong (..)
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.AffineFold (AffineFoldFl (..))
import Proarrow.Optic.AffineTraversal (AffineTravFl (..))
import Proarrow.Optic.Getter (GetterFl (..))
import Proarrow.Optic.Glass (GlassFl (..), applySel)
import Proarrow.Optic.Traversal (MonTravFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))
import Prelude (($))

-- | The tensor-action witness pair @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' m)@ views (and previews)
-- when the residual @m@ is a 'Comonoid': discard it with the counit. (Its setter and traversal
-- instances live in "Proarrow.Optic.Setter" and "Proarrow.Optic.Traversal".)
instance (Comonoid (m :: k)) => AffineFoldFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  previewP @_ @a (Rep h) = lft @k @a @TerminalObject . leftUnitor . (Mon.counit @m ** obj @a) . h

instance (Comonoid (m :: k)) => GetterFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  getP @_ @a (Rep h) = leftUnitor . (Mon.counit @m ** obj @a) . h

-- | In a cartesian category the tensor /is/ the product, so the comonoidal residual can be
-- projected out and put back: 'affineSet' and 'glassP' carry that assumption in their own
-- constraints ('Bicartesian', 'CCC'), which is why these instances exist while a 'LensFl' one
-- cannot ('putP' has only 'HasBinaryProducts').
instance (Comonoid (m :: k)) => AffineTravFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  -- a lens always matches
  affineMatch @_ @a @_ @t (Rep h) Objs = rgt @k @t @a . leftUnitor . (Mon.counit @m ** obj @a) . h
  affineSet @_ @a @b (Rep h) (Corep i) = i . first @b (fst @k @m @a . h)

instance (Comonoid (m :: k)) => GlassFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  glassP @s @a @b (Rep h@Objs) (Corep i) =
    withObExp @k @s @a $
      withObExp @k @(s ~~> a) @b $
        i
          . ( (fst @k @m @a . h . fst @k @s @((s ~~> a) ~~> b))
                &&& (applySel @s @a @b (snd @k @m @a . h) . snd @k @s @((s ~~> a) ~~> b))
            )

-- | The monoidal-lens flavor: a lens whose residual is a comonoid, so it is a
-- 'Proarrow.Optic.Getter.Getter' and a 'Proarrow.Optic.MonoidalTraversal.MonoidalTraversal', and
-- in cartesian categories an 'Proarrow.Optic.AffineTraversal.AffineTraversal' and a
-- 'Proarrow.Optic.Glass.Glass'.
type MonLensFl :: forall {k}. FLAVOR k k
class (GetterFl p q, MonTravFl p q, AffineTravFl p q, GlassFl p q) => MonLensFl (p :: k +-> k) (q :: k +-> k) where
  -- | Recover a monoidal lens's two legs and the comonoid structure of its existential residual
  -- @m@. The comonoid comes as a value ('ComonoidOn') rather than a 'Comonoid' constraint, because
  -- the residual of a composite is a tensor and that of the identity the unit, and type families
  -- cannot head an instance; symmetry is what makes a tensor of comonoids a comonoid.
  withMonLensP
    :: (SymMonoidal k)
    => p s a -> q b t -> (forall (m :: k). (Ob m) => ComonoidOn m -> (s ~> m ** a) -> (m ** b ~> t) -> r) -> r

instance (Comonoid (m :: k)) => MonLensFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  withMonLensP (Rep h) (Corep i) k = k @m (comonoidOn @m) h i

instance (CategoryOf k) => MonLensFl (Id :: k +-> k) (Id :: k +-> k) where
  withMonLensP (Id sa) (Id bt) k = k @Unit unitComonoid (leftUnitorInv . sa) (bt . leftUnitor) \\ sa \\ bt

instance
  forall k (f :: k +-> k) (f' :: k +-> k) (g :: k +-> k) (g' :: k +-> k)
   . (MonLensFl f g, MonLensFl f' g')
  => MonLensFl (f :.: f') (g' :.: g)
  where
  withMonLensP (f :.: (f'@Objs :: f' hix afoc)) ((g'@Objs :: g' bfoc giy) :.: g) kk =
    withMonLensP f g \ @(mo :: k) co ho io ->
      withMonLensP f' g' \ @(mi :: k) ci hi ii ->
        withOb2 @k @mo @mi
          ( kk @(mo ** mi)
              (tensorComonoid co ci)
              (associatorInv @k @mo @mi @afoc . (obj @mo ** hi) . ho)
              (io . (obj @mo ** ii) . associator @k @mo @mi @bfoc)
          )

type MonoidalLens (s :: k) (t :: k) a b = Optic (Prostrong MonLensFl) s t a b
type MonoidalLens' s a = MonoidalLens s s a a

-- | Build a monoidal lens from its two legs and a chosen __comonoidal__ residual @m@.
monLens
  :: forall {k} (m :: k) (s :: k) t a b
   . (Comonoid m, Ob a, Ob b) => (s ~> m ** a) -> (m ** b ~> t) -> MonoidalLens s t a b
monLens h i = legs2prof @MonLensFl (Rep @a @(ActionAt Tensor m) h) (Corep @b @(ActionAt Tensor m) i)

-- | Eliminate any optic that is at least an iso and at most a monoidal lens to its two legs,
-- recovering the existential residual @m@ together with its comonoid structure: run it at its
-- witness pair ('ExOptic' 'MonLensFl', via 'withLegs') and read the legs off with 'withMonLensP'.
withMonLens
  :: forall {k} c (s :: k) (t :: k) a b r
   . (SymMonoidal k, (Ob a, Ob b) => c (ExOptic MonLensFl a b))
  => Optic c s t a b -> (forall m. (Ob m) => ComonoidOn m -> (s ~> m ** a) -> (m ** b ~> t) -> r) -> r
withMonLens o k = withLegs @MonLensFl o \ @p @q p q -> withMonLensP @p @q p q \ @m co h i -> k @m co h i
