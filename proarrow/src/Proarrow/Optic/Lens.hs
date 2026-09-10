{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __lens__: the optic for the categorical product, with legs
--
-- > Lens s t a b = (s ~> a, (s && b) ~> t)
--
-- witnessed by @'Rep'@\/@'Corep'@ @('Product' s)@ ('LensRes' \/ 'putP') -- the product residual is
-- the whole source @s@. A lens both views and sets, sitting below 'Proarrow.Optic.Getter.Getter'
-- and 'Proarrow.Optic.AffineTraversal.AffineTraversal' in the lattice. Build with 'lens' (or from
-- the van-Laarhoven form with 'lensVL'), eliminate to the two legs with 'withLens', via the
-- generic 'ExOptic' carrier.
module Proarrow.Optic.Lens where

import Data.Functor.Const (Const (..))
import Prelude (const)
import Prelude qualified as P

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Functor (Functor (map), Prelude (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), Product, first)
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , SubFlavor (..)
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.AffineFold (AffineFoldRes)
import Proarrow.Optic.AffineTraversal (AffineTravRes (..))
import Proarrow.Optic.Fold (FoldRes)
import Proarrow.Optic.Getter (GetterRes (..))
import Proarrow.Optic.Setter (SetterRes)
import Proarrow.Optic.Traversal (TravRes)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (Rep (..))

type LensRes :: forall {k}. FLAVOR k k
class (AffineTravRes p q, GetterRes p q) => LensRes (p :: k +-> k) (q :: k +-> k) where
  -- | Like 'affineSet', but with an honest constraint: lens witnesses only ever need binary
  -- products, so lenses stay usable in categories without coproducts.
  putP :: (HasBinaryProducts k) => p (s :: k) a -> q b t -> (s && b) ~> t
instance (HasBinaryProducts k, Ob (s :: k)) => LensRes (Rep (Product s)) (Corep (Product s)) where
  putP @_ @a @b (Rep p) (Corep q) = q . first @b (fst @k @s @a . p)
instance (CategoryOf k) => LensRes (Id :: k +-> k) (Id :: k +-> k) where
  putP @s @_ @b sa (Id bt) = bt . snd @k @s @b \\ sa \\ bt
instance (LensRes f g, LensRes f' g') => LensRes (f :.: f') (g' :.: g) where
  putP @s @_ @b (f@Objs :.: f') (g'@Objs :.: g) =
    putP @f @g f g . (fst @_ @s @b &&& (putP @f' @g' f' g' . first @b (getP @f @g f)))

instance SubFlavor LensRes AffineTravRes where subFlavor r = r
instance SubFlavor LensRes GetterRes where subFlavor r = r
instance SubFlavor LensRes TravRes where subFlavor r = r
instance SubFlavor LensRes SetterRes where subFlavor r = r
instance SubFlavor LensRes AffineFoldRes where subFlavor r = r
instance SubFlavor LensRes FoldRes where subFlavor r = r

type Lens (s :: k) (t :: k) a b = Optic (Prostrong LensRes) s t a b
type Lens' s a = Lens s s a a
lens
  :: forall {k} (s :: k) (t :: k) a b
   . (HasBinaryProducts k, Ob b) => (s ~> a) -> ((s && b) ~> t) -> Lens s t a b
lens sa sbt =
  legs2prof @LensRes (Rep @a @(Product s) (id &&& sa)) (Corep @b @(Product s) sbt) \\ sa

-- | Eliminate any optic that is at least an iso and at most a lens to its two legs, in either
-- encoding: run it at its witness pair ('ExOptic' 'LensRes', via 'withLegs') and read the legs off
-- with 'getP' and 'putP'.
withLens
  :: forall {k} c (s :: k) (t :: k) a b r
   . (HasBinaryProducts k, (Ob a, Ob b) => c (ExOptic LensRes a b))
  => Optic c s t a b -> ((s ~> a) -> ((s && b) ~> t) -> r) -> r
withLens o k = withLegs @LensRes o \ @p @q p q -> k (getP @p @q p) (putP @p @q p q)

instance (P.Functor f) => Prostrong LensRes (Star (Prelude f)) where
  proact @p @q (p@Objs :.: Star f :.: q@Objs) = Star \a -> map (P.curry (putP p q) a) (f (getP @p @q p a))

type LensVL s t a b = forall f. (P.Functor f) => (a -> f b) -> s -> f t
toLensVL :: Lens s t a b -> LensVL s t a b
toLensVL (Optic l) = (unPrelude .) . unStar . l . Star . (Prelude .)

lensVL :: LensVL s t a b -> Lens s t a b
lensVL f = lens (getConst . f Const) (P.uncurry (f (const id)))
