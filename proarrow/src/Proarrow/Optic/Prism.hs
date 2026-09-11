{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __prism__: the optic for the coproduct, with legs
--
-- > Prism s t a b = (b ~> t, s ~> (t || a))
--
-- witnessed by @'Rep'@\/@'Corep'@ @('Coproduct' t)@ ('PrismFl' \/ 'matchingP'). A prism reviews
-- and matches, sitting below 'Proarrow.Optic.Getter.Review',
-- 'Proarrow.Optic.AffineTraversal.AffineTraversal' and
-- 'Proarrow.Optic.MonoidalTraversal.MonoidalTraversal' in the lattice. Build with 'prism',
-- eliminate to the two legs with 'withPrism' via the generic 'ExOptic' carrier;
-- 'toOpLens'\/'fromOpLens' witness the equivalence with the op-lens encoding, and this module also
-- hosts 'affineTraversal', the lens-then-prism builder for affine traversals.
module Proarrow.Optic.Prism where

import Proarrow.Category.Instance.Opposite (Op (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasBinaryCoproducts (..), HasCoproducts, left)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Flip
  , OpConstraint
  , Optic
  , Prostrong (..)
  , SubFlavor (..)
  , convert
  , legs2prof
  , opOptic
  , unOpOptic
  , withLegs
  , (%)
  )
import Proarrow.Optic.AffineFold (AffineFoldFl)
import Proarrow.Optic.AffineTraversal (AffineTravFl (..), AffineTraversal)
import Proarrow.Optic.Fold (FoldFl)
import Proarrow.Optic.Getter (GetterFl (..))
import Proarrow.Optic.Lens (Lens, LensFl, lens, withLens)
import Proarrow.Optic.Setter (SetterFl)
import Proarrow.Optic.Traversal (MonTravFl, TravFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

type PrismFl :: forall {k}. FLAVOR k k
class (AffineTravFl p q, GetterFl q p, MonTravFl p q) => PrismFl (p :: k +-> k) (q :: k +-> k) where
  -- | Like 'affineMatch', but with an honest constraint: prism witnesses only ever need binary
  -- coproducts, so prisms stay usable in categories without products.
  matchingP :: (HasBinaryCoproducts k) => p (s :: k) a -> q (b :: k) t -> s ~> (t || a)
instance (CopyDiscard k, HasCoproducts k, Ob t) => PrismFl (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  matchingP @_ @a @b (Rep p) (Corep q) = left @a (q . lft @k @t @b) . p
instance (CategoryOf k) => PrismFl (Id :: k +-> k) Id where
  matchingP @_ @a @_ @t (Id sa) bt = rgt @k @t @a . sa \\ sa \\ bt
instance (PrismFl f g, PrismFl f' g') => PrismFl (f :.: f') (g' :.: g) where
  matchingP @_ @a @_ @t (f :.: f'@Objs) (g' :.: g@Objs) =
    (lft @_ @t @a ||| (left @a (getP @g @f g) . matchingP @f' @g' f' g')) . matchingP @f @g f g

instance SubFlavor PrismFl AffineTravFl where subFlavor r = r
instance SubFlavor PrismFl MonTravFl where subFlavor r = r
instance SubFlavor PrismFl (Flip GetterFl) where subFlavor r = r
instance SubFlavor PrismFl TravFl where subFlavor r = r
instance SubFlavor PrismFl SetterFl where subFlavor r = r
instance SubFlavor PrismFl AffineFoldFl where subFlavor r = r
instance SubFlavor PrismFl FoldFl where subFlavor r = r

-- | A reversed prism views its build leg (@'getP'@ on the swapped pair): @'Proarrow.Optic.re' prism@ is a getter.
instance SubFlavor (Flip PrismFl) GetterFl where subFlavor r = r

instance SubFlavor (Flip PrismFl) AffineFoldFl where subFlavor r = r
instance SubFlavor (Flip PrismFl) FoldFl where subFlavor r = r

type Prism (s :: k) t a b = Optic (Prostrong PrismFl) s t a b
type Prism' s a = Prism s s a a
prism
  :: forall {k} (s :: k) (t :: k) a b
   . (CopyDiscard k, HasCoproducts k, Ob a) => (b ~> t) -> (s ~> (t || a)) -> Prism s t a b
prism bt sta =
  legs2prof @PrismFl (Rep @a @(Coproduct t) sta) (Corep @b @(Coproduct t) (id ||| bt)) \\ bt

-- | Build an 'AffineTraversal' by composing a 'Lens' with a 'Prism': focus a field with the lens,
-- then match a case of that field with the prism. There is no from-legs builder for a bare affine
-- traversal (its witness only ever arises by composition), so this is the design-aligned way to
-- make one -- the same @'convert' (l '%' p)@ idiom the test suite uses.
affineTraversal
  :: forall {k} (s :: k) t x y a b. (CategoryOf k) => Lens s t x y -> Prism x y a b -> AffineTraversal s t a b
affineTraversal l p = convert (l % p)

-- | Eliminate any optic that is at least an iso and at most a prism to its two legs, in either
-- encoding: run it at its witness pair ('ExOptic' 'PrismFl', via 'withLegs') and read the legs off
-- with 'matchingP' and 'getP' on the flipped pair (a prism's build leg is a getter read backwards).
withPrism
  :: forall {k} c (s :: k) (t :: k) a b r
   . (HasBinaryCoproducts k, (Ob a, Ob b) => c (ExOptic PrismFl a b))
  => Optic c s t a b -> ((b ~> t) -> (s ~> (t || a)) -> r) -> r
withPrism o k = withLegs @PrismFl o \ @p @q p q -> k (getP @q @p q) (matchingP @p @q p q)

-- | A 'Prism' and its op-lens encoding ('Proarrow.Optic.Lens.Prism', a 'Proarrow.Optic.Lens.Lens'
-- over the opposite category) carry the same data -- the two legs @(b '~>' t, s '~>' t '||' a)@ --
-- so they are equivalent. 'toOpLens' eliminates a 'PrismFl' prism to its legs (via 'Market') and
-- rebuilds the op-lens; 'fromOpLens' eliminates the op-lens (via 'Proarrow.Optic.Lens.withLens' on
-- 'opOptic', i.e. as a lens over 'Proarrow.Category.Instance.Opposite.OPPOSITE') and rebuilds the 'PrismFl' prism.
-- | The __op-lens__ encoding of a prism: a 'Proarrow.Optic.Lens.Lens' over the opposite category.
type OpLens (s :: k) t a b = Optic (OpConstraint (Prostrong LensFl)) s t a b

toOpLens :: forall {k} (s :: k) t a b. (HasCoproducts k, Ob a, Ob b) => Prism s t a b -> OpLens s t a b
toOpLens o = withPrism o (\bt sta -> unOpOptic (lens (Op bt) (Op sta)))

fromOpLens :: forall {k} (s :: k) t a b. (CopyDiscard k, HasCoproducts k, Ob a) => OpLens s t a b -> Prism s t a b
fromOpLens o = withLens (opOptic o) (\rev match -> prism (unOp rev) (unOp match))
