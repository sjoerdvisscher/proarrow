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
-- > Lens         <: { Getter, AffineTraversal }      -- product residual
-- > MonoidalLens <: { Getter, MonoidalTraversal }    -- comonoidal tensor residual
--
-- Crucially it asks 'Comonoid' of __the residual only__, not
-- 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' of the whole category: it works in every
-- @CopyDiscard@ category (there every object is a comonoid) /and/ in genuinely non-cartesian ones
-- like @LINEAR@ for the residuals that are comonoids (the duplicable @Ur@ objects). The ordinary
-- 'Proarrow.Optic.Lens.Lens' is the @tensor = product@ specialization, where the residual is
-- recoverable from @s@ by projection.
module Proarrow.Optic.MonoidalLens where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Colimit.BinaryCoproduct (lft)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid)
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
import Proarrow.Optic.AffineFold (AffineFoldFl (..))
import Proarrow.Optic.Fold (FoldFl)
import Proarrow.Optic.Getter (GetterFl (..))
import Proarrow.Optic.Setter (SetterFl)
import Proarrow.Optic.Traversal (MonTravFl, TravFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | The tensor-action witness pair @'Rep'@\/@'Corep'@ @('ActionAt' 'Tensor' m)@ views (and previews)
-- when the residual @m@ is a 'Comonoid': discard it with the counit. (Its setter and traversal
-- instances live in "Proarrow.Optic.Setter" and "Proarrow.Optic.Traversal".)
instance (Comonoid (m :: k)) => AffineFoldFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  previewP @_ @a (Rep h) = lft @k @a @TerminalObject . leftUnitor . (Mon.counit @m ** obj @a) . h

instance (Comonoid (m :: k)) => GetterFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  getP @_ @a (Rep h) = leftUnitor . (Mon.counit @m ** obj @a) . h

-- | The monoidal-lens flavor: a lens whose residual is a comonoid, so it is both a
-- 'Proarrow.Optic.Getter.Getter' and a 'Proarrow.Optic.MonoidalTraversal.MonoidalTraversal'.
type MonLensFl :: forall {k}. FLAVOR k k
class (GetterFl p q, MonTravFl p q) => MonLensFl (p :: k +-> k) (q :: k +-> k) where
  -- | Recover a monoidal lens's two legs, with the (comonoidal) residual @m@ existential.
  withMonLensP :: (Monoidal k) => p s a -> q b t -> (forall (m :: k). (Ob m) => (s ~> m ** a) -> (m ** b ~> t) -> r) -> r

instance (Comonoid (m :: k)) => MonLensFl (Rep (ActionAt Tensor m) :: k +-> k) (Corep (ActionAt Tensor m)) where
  withMonLensP (Rep h) (Corep i) k = k @m h i

instance (CategoryOf k) => MonLensFl (Id :: k +-> k) (Id :: k +-> k) where
  withMonLensP (Id sa) (Id bt) k = k @Unit (leftUnitorInv . sa) (bt . leftUnitor) \\ sa \\ bt

instance
  forall k (f :: k +-> k) (f' :: k +-> k) (g :: k +-> k) (g' :: k +-> k)
   . (MonLensFl f g, MonLensFl f' g')
  => MonLensFl (f :.: f') (g' :.: g)
  where
  withMonLensP (f :.: (f' :: f' hix afoc)) ((g' :: g' bfoc giy) :.: g) kk =
    withMonLensP f g \ @(mo :: k) ho io ->
      withMonLensP f' g' \ @(mi :: k) hi ii ->
        withOb2 @k @mo @mi
          ( kk @(mo ** mi)
              (associatorInv @k @mo @mi @afoc . (obj @mo ** hi) . ho)
              (io . (obj @mo ** ii) . associator @k @mo @mi @bfoc)
          )
          \\ f'
          \\ g'

instance SubFlavor MonLensFl GetterFl where subFlavor r = r
instance SubFlavor MonLensFl MonTravFl where subFlavor r = r
instance SubFlavor MonLensFl TravFl where subFlavor r = r
instance SubFlavor MonLensFl SetterFl where subFlavor r = r
instance SubFlavor MonLensFl AffineFoldFl where subFlavor r = r
instance SubFlavor MonLensFl FoldFl where subFlavor r = r

type MonoidalLens (s :: k) (t :: k) a b = Optic (Prostrong MonLensFl) s t a b
type MonoidalLens' s a = MonoidalLens s s a a

-- | Build a monoidal lens from its two legs and a chosen __comonoidal__ residual @m@.
monLens
  :: forall {k} (m :: k) (s :: k) t a b
   . (Comonoid m, Ob a, Ob b) => (s ~> m ** a) -> (m ** b ~> t) -> MonoidalLens s t a b
monLens h i = legs2prof @MonLensFl (Rep @a @(ActionAt Tensor m) h) (Corep @b @(ActionAt Tensor m) i)

-- | Eliminate any optic that is at least an iso and at most a monoidal lens to its two legs,
-- recovering the existential residual @m@: run it at its witness pair ('ExOptic' 'MonLensFl', via
-- 'withLegs') and read the legs off with 'withMonLensP'.
withMonLens
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, (Ob a, Ob b) => c (ExOptic MonLensFl a b))
  => Optic c s t a b -> (forall m. (Ob m) => (s ~> m ** a) -> (m ** b ~> t) -> r) -> r
withMonLens o k = withLegs @MonLensFl o \ @p @q p q -> withMonLensP @p @q p q \ @m h i -> k @m h i
