{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Optic.Iso where

import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), type (+->))
import Proarrow.Optic
  ( CompactFlavor
  , FLAVOR
  , Flip
  , Optic
  , Optic_ (..)
  , PIso
  , Prostrong (..)
  , SubFlavor (..)
  , convert
  , iso
  )
import Proarrow.Optic.AffineFold (AffineFoldRes)
import Proarrow.Optic.AffineTraversal (AffineTravRes)
import Proarrow.Optic.Fold (FoldRes)
import Proarrow.Optic.Getter (GetterRes, getP)
import Proarrow.Optic.Grate (GrateRes)
import Proarrow.Optic.Kaleidoscope (KaleidoRes)
import Proarrow.Optic.Lens (LensRes)
import Proarrow.Optic.MonoidalLens (MonLensRes)
import Proarrow.Optic.Prism (PrismRes)
import Proarrow.Optic.Setter (SetterRes)
import Proarrow.Optic.Traversal (TravRes)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

class (LensRes p q, PrismRes p q, KaleidoRes p q, MonLensRes p q) => IsoRes p q
instance (LensRes p q, PrismRes p q, KaleidoRes p q, MonLensRes p q) => IsoRes p q

instance CompactFlavor IsoRes

-- | The 'Prostrong'-flavored iso; for the profunctor-class-flavored encoding see 'Proarrow.Optic.PIso'.
type Iso (s :: k) (t :: k) a b = Optic (Prostrong IsoRes) s t a b

type Iso' s a = Iso s s a a

instance SubFlavor IsoRes LensRes where subFlavor r = r
instance SubFlavor IsoRes PrismRes where subFlavor r = r
instance SubFlavor IsoRes AffineTravRes where subFlavor r = r
instance SubFlavor IsoRes GetterRes where subFlavor r = r
instance SubFlavor IsoRes (Flip GetterRes) where subFlavor r = r
instance SubFlavor IsoRes TravRes where subFlavor r = r
instance SubFlavor IsoRes SetterRes where subFlavor r = r
instance SubFlavor IsoRes AffineFoldRes where subFlavor r = r
instance SubFlavor IsoRes FoldRes where subFlavor r = r
instance SubFlavor IsoRes GrateRes where subFlavor r = r
instance SubFlavor IsoRes KaleidoRes where subFlavor r = r
instance SubFlavor IsoRes MonLensRes where subFlavor r = r

-- | Reversed isos still view\/preview\/fold: @'Proarrow.Optic.re' iso@ is a getter (and more).
instance SubFlavor (Flip IsoRes) GetterRes where subFlavor r = r

instance SubFlavor (Flip IsoRes) AffineFoldRes where subFlavor r = r
instance SubFlavor (Flip IsoRes) FoldRes where subFlavor r = r

-- | Any flavor whose optics are isos has strength for the 'Yo' profunctor.
instance (CategoryOf k, SubFlavor w IsoRes) => Prostrong (w :: FLAVOR k k) (Yo a (OP b) :: k +-> k) where
  proact @f @g (f :.: Yo sa bt :.: g) =
    subFlavor @w @IsoRes @f @g (Yo (sa . getP @f @g f) (getP @g @f g . bt))

-- | 'Proarrow.Optic.re'-versed isos are still isos: the same carrier eliminates them by reading
-- the witness pair backwards. This is a conversion the 'SubFlavor' lattice cannot express (the
-- entailment @IsoRes q p => IsoRes p q@ doesn't hold), but the carrier can compute it.
instance {-# OVERLAPPING #-} (CategoryOf k) => Prostrong (Flip IsoRes) (Yo (a :: k) (OP b) :: k +-> k) where
  proact @f @g (f :.: Yo sa bt :.: g) = Yo (sa . getP @f @g f) (getP @g @f g . bt)

-- | Eliminate any iso-flavored optic to its two legs, in either encoding -- including the
-- profunctor-class-flavored 'Proarrow.Optic.PIso' and reversed ('Proarrow.Optic.re') isos.
withIso
  :: forall {k} c (s :: k) (t :: k) a b r
   . (CategoryOf k, (Ob a, Ob b) => c (Yo a (OP b)))
  => Optic c s t a b -> ((s ~> a) -> (b ~> t) -> r) -> r
withIso (Optic l) k = case l @(Yo a (OP b)) (Yo id id) of Yo sa bt -> k sa bt

-- | The two iso encodings are equivalent: this direction instantiates the
-- profunctor-class-flavored iso at the free 'IsoRes'-strong profunctor @ExOptic 'IsoRes' a b@,
-- which needs nothing beyond its 'Profunctor' instance.
fromPIso :: forall {k} (s :: k) (t :: k) a b. (CategoryOf k) => PIso s t a b -> Iso s t a b
fromPIso = convert

-- | The other direction of the equivalence, by eliminating to legs and rebuilding.
toPIso :: forall {k} (s :: k) (t :: k) a b. (CategoryOf k) => Iso s t a b -> PIso s t a b
toPIso o = withIso o iso
