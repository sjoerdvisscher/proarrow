{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Optic.Prism where

import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasBinaryCoproducts (..), HasCoproducts, left)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( CompactFlavor
  , ExOptic (..)
  , FLAVOR
  , Flip
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , SubFlavor (..)
  , ex2prof
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
import Proarrow.Profunctor.Representable (Rep (..))

type PrismRes :: forall {k}. FLAVOR k k
class (AffineTravRes p q, GetterRes q p) => PrismRes (p :: k +-> k) (q :: k +-> k) where
  -- | Like 'affineMatch', but with an honest constraint: prism witnesses only ever need binary
  -- coproducts, so prisms stay usable in categories without products.
  matchingP :: (HasBinaryCoproducts k) => p (s :: k) a -> q (b :: k) t -> s ~> (t || a)
instance (HasCoproducts k, Ob t) => PrismRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  matchingP @_ @a @b (Rep p) (Corep q) = left @a (q . lft @k @t @b) . p
instance (CategoryOf k) => PrismRes (Id :: k +-> k) Id where
  matchingP @_ @a @_ @t (Id sa) bt = rgt @k @t @a . sa \\ sa \\ bt
instance (PrismRes f g, PrismRes f' g') => PrismRes (f :.: f') (g' :.: g) where
  matchingP @_ @a @_ @t (f :.: f'@Objs) (g' :.: g@Objs) =
    (lft @_ @t @a ||| (left @a (getP @g @f g) . matchingP @f' @g' f' g')) . matchingP @f @g f g

instance CompactFlavor PrismRes

instance SubFlavor PrismRes AffineTravRes where subFlavor r = r
instance SubFlavor PrismRes (Flip GetterRes) where subFlavor r = r
instance SubFlavor PrismRes TravRes where subFlavor r = r
instance SubFlavor PrismRes SetterRes where subFlavor r = r
instance SubFlavor PrismRes AffineFoldRes where subFlavor r = r
instance SubFlavor PrismRes FoldRes where subFlavor r = r

-- | A reversed prism views its build leg (@'getP'@ on the swapped pair): @'Proarrow.Optic.re' prism@ is a getter.
instance SubFlavor (Flip PrismRes) GetterRes where subFlavor r = r

instance SubFlavor (Flip PrismRes) AffineFoldRes where subFlavor r = r
instance SubFlavor (Flip PrismRes) FoldRes where subFlavor r = r

type Prism (s :: k) t a b = Optic (Prostrong PrismRes) s t a b
type Prism' s a = Prism s s a a
prism :: forall {k} (s :: k) (t :: k) a b. (HasCoproducts k, Ob a) => (b ~> t) -> (s ~> (t || a)) -> Prism s t a b
prism bt sta =
  ex2prof (ExProstrong @(Rep (Coproduct t)) @(Corep (Coproduct t)) (Rep sta :.: ExIso id id :.: Corep (id ||| bt))) \\ bt

-- | The eliminating carrier for prisms: a prism's two legs, as a profunctor in @s@\/@t@.
type Market :: forall {k}. k -> k -> k +-> k
data Market a b s t where
  Market :: (Ob a, Ob b) => (b ~> t) -> (s ~> (t || a)) -> Market a b s t

instance (HasBinaryCoproducts k, Ob (a :: k), Ob b) => Profunctor (Market a b :: k +-> k) where
  dimap l r (Market bt sta) = Market (r . bt) (left @a r . sta . l) \\ l \\ r
  r \\ Market bt sta = r \\ bt \\ sta

-- | Any flavor whose optics have prism legs has strength for the 'Market' carrier.
instance (HasBinaryCoproducts k, Ob (a :: k), Ob b, SubFlavor w PrismRes) => Prostrong (w :: FLAVOR k k) (Market a b :: k +-> k) where
  proact @f @g @_ @t (f@Objs :.: Market bt sta :.: g@Objs) =
    subFlavor @w @PrismRes @f @g
      (Market (getP @g @f g . bt) ((lft @_ @t @a ||| (left @a (getP @g @f g) . sta)) . matchingP @f @g f g))

-- | Eliminate any optic that is at least an iso and at most a prism to its two legs, in either
-- encoding.
withPrism
  :: forall {k} c (s :: k) (t :: k) a b r
   . (HasBinaryCoproducts k, (Ob a, Ob b) => c (Market a b))
  => Optic c s t a b -> ((b ~> t) -> (s ~> (t || a)) -> r) -> r
withPrism (Optic l) k = case l @(Market a b) (Market id (rgt @k @b @a)) of Market bt sta -> k bt sta

