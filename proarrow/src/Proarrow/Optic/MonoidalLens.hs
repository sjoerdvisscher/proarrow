{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __monoidal lens__: the coend optic for the tensor action,
--
-- > MonoidalLens s t a b = exists m. (s ~> m ** a, m ** b ~> t)
--
-- The residual @m@ is carried through the tensor and __never discarded__, so a monoidal lens needs
-- only 'Monoidal' -- no products, no 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard'. Its
-- witness pair is exactly 'Proarrow.Optic.MonoidalTraversal.TensorW'\/'Proarrow.Optic.MonoidalTraversal.CoTensorW'.
--
-- Because the residual is carried rather than projected, a monoidal lens can @'Proarrow.Optic.Setter.over'@\/modify
-- with only 'Monoidal', but can only /view/ or /fold/ where the category is
-- 'Proarrow.Category.Monoidal.CopyDiscard.CopyDiscard' (view = discard the residual). It is
-- therefore a 'Proarrow.Optic.Setter.SetterRes' unconditionally, and gains the traversal\/fold\/view
-- capability through the explicit @CopyDiscard@ bridges below ('monLensToMonTraversal', 'viewMon'),
-- not through a 'SubFlavor'. The ordinary 'Proarrow.Optic.Lens.Lens' is the @tensor = product@
-- specialization, where @m@ is recoverable from @s@ and the classical get\/put laws return.
module Proarrow.Optic.MonoidalLens where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (\\), type (+->))
import Proarrow.Optic
  ( ExOptic (..)
  , FLAVOR
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , SubFlavor (..)
  , ex2prof
  )
import Proarrow.Optic.MonoidalTraversal (CoTensorW (..), MonoidalTraversal, TensorW (..))
import Proarrow.Optic.Setter (SetterRes (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

-- | The monoidal-lens flavor: a 'Proarrow.Optic.Setter.SetterRes' whose witness carries a single
-- existential tensor residual, recoverable as the two legs @(s ~> m ** a, m ** b ~> t)@.
type MonLensRes :: forall {k}. FLAVOR k k
class (SetterRes p q) => MonLensRes (p :: k +-> k) (q :: k +-> k) where
  -- | Recover a monoidal lens's two legs, with the residual @m@ existential. Needs only
  -- 'Monoidal' -- the residual is threaded, never discarded.
  withMonLensP :: (Monoidal k) => p s a -> q b t -> (forall (m :: k). (Ob m) => (s ~> m ** a) -> (m ** b ~> t) -> r) -> r

instance (Monoidal k, Ob (m :: k)) => MonLensRes (TensorW m :: k +-> k) (CoTensorW m) where
  withMonLensP (TensorW h) (CoTensorW i) k = k @m h i

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

instance SubFlavor MonLensRes SetterRes where subFlavor r = r

type MonoidalLens (s :: k) (t :: k) a b = Optic (Prostrong MonLensRes) s t a b
type MonoidalLens' s a = MonoidalLens s s a a

-- | Build a monoidal lens from its two legs and a chosen residual @m@.
monLens
  :: forall {k} (m :: k) (s :: k) t a b
   . (Monoidal k, Ob m, Ob a, Ob b) => (s ~> m ** a) -> (m ** b ~> t) -> MonoidalLens s t a b
monLens h i = ex2prof (ExProstrong @(TensorW m) @(CoTensorW m) (TensorW h :.: ExIso id id :.: CoTensorW i))

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

-- * Bridges to the fold\/traversal side, available only under 'CopyDiscard'

-- | A monoidal lens is a 'MonoidalTraversal' once the residual can be discarded.
monLensToMonTraversal
  :: forall {k} (s :: k) t a b
   . (CopyDiscard k, Ob a, Ob b)
  => MonoidalLens s t a b -> MonoidalTraversal s t a b
monLensToMonTraversal o =
  withMonLens o \ @m h i -> ex2prof (ExProstrong @(TensorW m) @(CoTensorW m) (TensorW h :.: ExIso id id :.: CoTensorW i))

-- | View a monoidal lens's focus, discarding the residual. Needs 'CopyDiscard'.
viewMon :: forall {k} (s :: k) t a b. (CopyDiscard k, Ob a) => MonoidalLens s t a b -> s ~> a
viewMon o = withMonLens o \ @m h _ -> leftUnitor . (discard @k @m ** obj @a) . h
