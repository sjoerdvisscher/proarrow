{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __iso__: the bottom of the subtyping lattice, usable as every other flavor. 'IsoFl' is
-- simply the conjunction of the five maximal flavors ('Proarrow.Optic.Lens.LensFl',
-- 'Proarrow.Optic.Prism.PrismFl', 'Proarrow.Optic.PowerGrate.PowerGrateFl',
-- 'Proarrow.Optic.MonoidalLens.MonLensFl' and 'Proarrow.Optic.Tracer.TracerFl'). Build with 'iso', eliminate to the two legs with
-- 'withIso' via the 'Yo' carrier -- which also eliminates 'Proarrow.Optic.re'-versed isos, a
-- conversion the 'SubFlavor' lattice itself cannot express; 'fromPIso'\/'toPIso' mediate with the
-- profunctor-class-flavored 'PIso'.
module Proarrow.Optic.Iso where

import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), type (+->))
import Proarrow.Optic
  ( FLAVOR
  , Flip
  , Optic
  , Optic_ (..)
  , PIso
  , Prostrong (..)
  , SubFlavor (..)
  , convert
  , iso
  )
import Proarrow.Optic.AffineFold (AffineFoldFl)
import Proarrow.Optic.AffineTraversal (AffineTravFl)
import Proarrow.Optic.Fold (FoldFl)
import Proarrow.Optic.Getter (GetterFl, getP)
import Proarrow.Optic.Grate (GrateFl)
import Proarrow.Optic.Lens (LensFl)
import Proarrow.Optic.MonoidalLens (MonLensFl)
import Proarrow.Optic.PowerGrate (PowerGrateFl)
import Proarrow.Optic.Prism (PrismFl)
import Proarrow.Optic.Setter (SetterFl)
import Proarrow.Optic.Tracer (TracerFl)
import Proarrow.Optic.Traversal (TravFl)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

class (LensFl p q, PrismFl p q, PowerGrateFl p q, MonLensFl p q, TracerFl p q) => IsoFl p q
instance (LensFl p q, PrismFl p q, PowerGrateFl p q, MonLensFl p q, TracerFl p q) => IsoFl p q

-- | The 'Prostrong'-flavored iso; for the profunctor-class-flavored encoding see 'Proarrow.Optic.PIso'.
type Iso (s :: k) (t :: k) a b = Optic (Prostrong IsoFl) s t a b

type Iso' s a = Iso s s a a

instance SubFlavor IsoFl LensFl where subFlavor r = r
instance SubFlavor IsoFl PrismFl where subFlavor r = r
instance SubFlavor IsoFl AffineTravFl where subFlavor r = r
instance SubFlavor IsoFl GetterFl where subFlavor r = r
instance SubFlavor IsoFl (Flip GetterFl) where subFlavor r = r
instance SubFlavor IsoFl TravFl where subFlavor r = r
instance SubFlavor IsoFl SetterFl where subFlavor r = r
instance SubFlavor IsoFl AffineFoldFl where subFlavor r = r
instance SubFlavor IsoFl FoldFl where subFlavor r = r
instance SubFlavor IsoFl GrateFl where subFlavor r = r
instance SubFlavor IsoFl PowerGrateFl where subFlavor r = r
instance SubFlavor IsoFl MonLensFl where subFlavor r = r
instance SubFlavor IsoFl TracerFl where subFlavor r = r

-- | Reversed isos still view\/preview\/fold: @'Proarrow.Optic.re' iso@ is a getter (and more).
instance SubFlavor (Flip IsoFl) GetterFl where subFlavor r = r

instance SubFlavor (Flip IsoFl) AffineFoldFl where subFlavor r = r
instance SubFlavor (Flip IsoFl) FoldFl where subFlavor r = r

-- | Any flavor whose optics are isos has strength for the 'Yo' profunctor.
instance (CategoryOf k, SubFlavor w IsoFl) => Prostrong (w :: FLAVOR k k) (Yo a (OP b) :: k +-> k) where
  proact @f @g (f :.: Yo sa bt :.: g) =
    subFlavor @w @IsoFl @f @g (Yo (sa . getP @f @g f) (getP @g @f g . bt))

-- | 'Proarrow.Optic.re'-versed isos are still isos: the same carrier eliminates them by reading
-- the witness pair backwards. This is a conversion the 'SubFlavor' lattice cannot express (the
-- entailment @IsoFl q p => IsoFl p q@ doesn't hold), but the carrier can compute it.
instance {-# OVERLAPPING #-} (CategoryOf k) => Prostrong (Flip IsoFl) (Yo (a :: k) (OP b) :: k +-> k) where
  proact @f @g (f :.: Yo sa bt :.: g) = Yo (sa . getP @f @g f) (getP @g @f g . bt)

-- | Eliminate any iso-flavored optic to its two legs, in either encoding -- including the
-- profunctor-class-flavored 'Proarrow.Optic.PIso' and reversed ('Proarrow.Optic.re') isos.
withIso
  :: forall {k} c (s :: k) (t :: k) a b r
   . (CategoryOf k, (Ob a, Ob b) => c (Yo a (OP b)))
  => Optic c s t a b -> ((s ~> a) -> (b ~> t) -> r) -> r
withIso (Optic l) k = case l @(Yo a (OP b)) (Yo id id) of Yo sa bt -> k sa bt

-- | The two iso encodings are equivalent: this direction instantiates the
-- profunctor-class-flavored iso at the free 'IsoFl'-strong profunctor @ExOptic 'IsoFl' a b@,
-- which needs nothing beyond its 'Proarrow.Core.Profunctor' instance.
fromPIso :: forall {k} (s :: k) (t :: k) a b. (CategoryOf k) => PIso s t a b -> Iso s t a b
fromPIso = convert

-- | The other direction of the equivalence, by eliminating to legs and rebuilding.
toPIso :: forall {k} (s :: k) (t :: k) a b. (CategoryOf k) => Iso s t a b -> PIso s t a b
toPIso o = withIso o iso
