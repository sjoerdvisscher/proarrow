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

import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Tensor)
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Colimit.BinaryCoproduct (lft)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid)
import Proarrow.Monoid qualified as Mon
import Proarrow.Optic
  ( ExOptic (..)
  , FLAVOR
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , SubFlavor (..)
  , ex2prof
  )
import Proarrow.Optic.AffineFold (AffineFoldRes (..))
import Proarrow.Optic.Fold (FoldRes (..))
import Proarrow.Optic.Getter (GetterRes (..))
import Proarrow.Optic.Setter (SetterRes (..))
import Proarrow.Optic.Traversal (MonTravRes (..), TravRes (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

-- | Witness pair for a monoidal lens: the focus @a@ sits inside @m ** a@ with a __comonoidal__
-- residual @m@. Being a comonoid, @m@ can be discarded (for @get@\/fold) and carried (for @set@).
type LensW :: forall {k}. k -> k +-> k
data LensW m s a where
  LensW :: (Comonoid m, Ob a) => (s ~> (m ** a)) -> LensW m s a

type CoLensW :: forall {k}. k -> k +-> k
data CoLensW m b t where
  CoLensW :: (Comonoid m, Ob b) => ((m ** b) ~> t) -> CoLensW m b t

instance (Comonoid (m :: k)) => Profunctor (LensW m :: k +-> k) where
  dimap l r (LensW h) = LensW ((obj @m ** r) . h . l) \\ r
  r \\ LensW h = r \\ h
instance (Comonoid (m :: k)) => Profunctor (CoLensW m :: k +-> k) where
  dimap l r (CoLensW i) = CoLensW (r . i . (obj @m ** l)) \\ l
  r \\ CoLensW i = r \\ i

instance (Comonoid (m :: k)) => Proadjunction (LensW m :: k +-> k) (CoLensW m) where
  unit @c = withOb2 @k @m @c (CoLensW id :.: LensW id)
  counit (LensW h :.: CoLensW i) = i . h
instance (Comonoid (m :: k)) => SetterRes (LensW m :: k +-> k) (CoLensW m) where
  overP (LensW h) (CoLensW i) f = i . (obj @m ** f) . h
instance (Comonoid (m :: k)) => FoldRes (LensW m :: k +-> k) (CoLensW m) where
  foldMapP (LensW h) am = leftUnitor . (Mon.counit @m ** am) . h
instance (Comonoid (m :: k)) => AffineFoldRes (LensW m :: k +-> k) (CoLensW m) where
  previewP @_ @a (LensW h) = lft @k @a @TerminalObject . leftUnitor . (Mon.counit @m ** obj @a) . h
instance (Comonoid (m :: k)) => GetterRes (LensW m :: k +-> k) (CoLensW m) where
  getP @_ @a (LensW h) = leftUnitor . (Mon.counit @m ** obj @a) . h
instance (Comonoid (m :: k)) => TravRes (LensW m :: k +-> k) (CoLensW m)
instance (Comonoid (m :: k)) => MonTravRes (LensW m :: k +-> k) (CoLensW m) where
  monTravP (LensW h) (CoLensW i) r = dimap h i (act @Tensor @_ @m r)

-- | The monoidal-lens flavor: a lens whose residual is a comonoid, so it is both a
-- 'Proarrow.Optic.Getter.Getter' and a 'Proarrow.Optic.MonoidalTraversal.MonoidalTraversal'.
type MonLensRes :: forall {k}. FLAVOR k k
class (GetterRes p q, MonTravRes p q) => MonLensRes (p :: k +-> k) (q :: k +-> k) where
  -- | Recover a monoidal lens's two legs, with the (comonoidal) residual @m@ existential.
  withMonLensP :: (Monoidal k) => p s a -> q b t -> (forall (m :: k). (Ob m) => (s ~> m ** a) -> (m ** b ~> t) -> r) -> r

instance (Comonoid (m :: k)) => MonLensRes (LensW m :: k +-> k) (CoLensW m) where
  withMonLensP (LensW h) (CoLensW i) k = k @m h i

instance (CategoryOf k) => MonLensRes (Id :: k +-> k) (Id :: k +-> k) where
  withMonLensP (Id sa) (Id bt) k = k @Unit (leftUnitorInv . sa) (bt . leftUnitor) \\ sa \\ bt

instance
  forall k (f :: k +-> k) (f' :: k +-> k) (g :: k +-> k) (g' :: k +-> k)
   . (MonLensRes f g, MonLensRes f' g')
  => MonLensRes (f :.: f') (g' :.: g)
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

instance SubFlavor MonLensRes GetterRes where subFlavor r = r
instance SubFlavor MonLensRes MonTravRes where subFlavor r = r
instance SubFlavor MonLensRes TravRes where subFlavor r = r
instance SubFlavor MonLensRes SetterRes where subFlavor r = r
instance SubFlavor MonLensRes AffineFoldRes where subFlavor r = r
instance SubFlavor MonLensRes FoldRes where subFlavor r = r

type MonoidalLens (s :: k) (t :: k) a b = Optic (Prostrong MonLensRes) s t a b
type MonoidalLens' s a = MonoidalLens s s a a

-- | Build a monoidal lens from its two legs and a chosen __comonoidal__ residual @m@.
monLens
  :: forall {k} (m :: k) (s :: k) t a b
   . (Comonoid m, Ob a, Ob b) => (s ~> m ** a) -> (m ** b ~> t) -> MonoidalLens s t a b
monLens h i = ex2prof (ExProstrong @(LensW m) @(CoLensW m) (LensW h :.: ExIso id id :.: CoLensW i))

-- | The eliminating carrier for monoidal lenses: the two legs with the residual @m@ existential.
type MonShop :: forall {k}. k -> k -> k +-> k
data MonShop a b s t where
  MonShop :: (Ob a, Ob b, Ob m) => (s ~> m ** a) -> (m ** b ~> t) -> MonShop a b s t

instance (Monoidal k, Ob (a :: k), Ob b) => Profunctor (MonShop a b :: k +-> k) where
  dimap l r (MonShop @_ @_ @m h i) = MonShop @a @b @m (h . l) (r . i) \\ l \\ r
  r \\ MonShop h i = r \\ h \\ i

-- | Any flavor whose optics have monoidal-lens legs has strength for the 'MonShop' carrier:
-- absorbing a witness pair combines its residual with the carrier's by tensoring.
instance (Monoidal k, Ob (a :: k), Ob b, SubFlavor w MonLensRes) => Prostrong (w :: FLAVOR k k) (MonShop a b :: k +-> k) where
  proact @f @g (f :.: MonShop @_ @_ @m h i :.: g) =
    subFlavor @w @MonLensRes @f @g
      ( withMonLensP f g \ @mf hf ir ->
          withOb2 @k @mf @m
            ( MonShop @a @b @(mf ** m)
                (associatorInv @k @mf @m @a . (obj @mf ** h) . hf)
                (ir . (obj @mf ** i) . associator @k @mf @m @b)
            )
      )

-- | Eliminate any optic that is at least an iso and at most a monoidal lens to its two legs,
-- recovering the existential residual @m@.
withMonLens
  :: forall {k} c (s :: k) (t :: k) a b r
   . (Monoidal k, (Ob a, Ob b) => c (MonShop a b))
  => Optic c s t a b -> (forall m. (Ob m) => (s ~> m ** a) -> (m ** b ~> t) -> r) -> r
withMonLens (Optic l) k = case l @(MonShop a b) (MonShop @a @b @Unit leftUnitorInv leftUnitor) of
  MonShop @_ @_ @m h i -> k @m h i
