{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __affine traversal__: the 0-or-1 focus optic that can also reconstruct, the meet of
-- 'Proarrow.Optic.Lens.Lens' and 'Proarrow.Optic.Prism.Prism' in the subtyping lattice. Its two
-- legs are 'affineMatch' @:: s ~> (t || a)@ and 'affineSet' @:: (s && b) ~> t@ ('AffineTravFl').
-- Its witnesses only ever arise by composing lens and prism witnesses, so it is built with
-- 'Proarrow.Optic.Prism.affineTraversal' (a 'Proarrow.Optic.Lens.Lens' followed by a
-- 'Proarrow.Optic.Prism.Prism') and eliminated with 'matching', via the generic 'Proarrow.Optic.ExOptic' carrier.
module Proarrow.Optic.AffineTraversal where

import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), first, second)
import Proarrow.Category.Monoidal.Cartesian (Bicartesian, productToTensor, tensorToProduct)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..), fst, snd, (&&&))
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasBinaryCoproducts (..), HasCoproducts, left)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (type (&&)), Product)
import Proarrow.Limit.BinaryProduct qualified as P
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (ExOptic, FLAVOR, Optic, Prostrong (..), withLegs)
import Proarrow.Optic.AffineFold (AffineFoldFl)
import Proarrow.Optic.Traversal (TravFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

type AffineTravFl :: forall {k}. FLAVOR k k
class (TravFl p q, AffineFoldFl p q) => AffineTravFl (p :: k +-> k) (q :: k +-> k) where
  affineMatch :: (Bicartesian k) => p (s :: k) a -> q b t -> s ~> (t || a)
  affineSet :: (Bicartesian k) => p (s :: k) a -> q b t -> (s && b) ~> t
instance (HasBinaryProducts k, Ob (s :: k)) => AffineTravFl (Rep (Product s)) (Corep (Product s)) where
  -- a lens always matches
  affineMatch @_ @a @_ @t (Rep p) q = rgt @k @t @a . P.snd @k @s @a . p \\ p \\ q
  affineSet @_ @a @b (Rep p) (Corep q) = q . P.first @b (P.fst @k @s @a . p)
instance (CopyDiscard k, HasCoproducts k, Ob t) => AffineTravFl (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  affineMatch @_ @a @b (Rep p) (Corep q) = left @a (q . lft @k @t @b) . p

  -- a prism's set never needs the original value, it just reviews
  affineSet @s @_ @b (Rep p) (Corep q) = q . rgt @k @t @b . P.snd @k @s @b \\ p
instance (CategoryOf k) => AffineTravFl (Id :: k +-> k) (Id :: k +-> k) where
  affineMatch @_ @a @_ @t (Id sa) bt = rgt @k @t @a . sa \\ sa \\ bt
  affineSet @s @_ @b sa (Id bt) = bt . P.snd @k @s @b \\ sa \\ bt
instance (AffineTravFl f g, AffineTravFl f' g') => AffineTravFl (f :.: f') (g' :.: g) where
  -- match the outer; on failure of the inner, reconstruct via the outer's own setter, reusing s
  affineMatch @s @a @_ @t ((:.:) @m f@Objs f'@Objs) ((:.:) @n g'@Objs g@Objs) =
    ( (lft @_ @t @a . snd @s @t)
        ||| ( ((lft @_ @t @a . affineSet @f @g f g . tensorToProduct @s @n) ||| (rgt @_ @t @a . snd @s @a))
                . distL @_ @s @n @a
                . second @s (affineMatch @f' @g' f' g')
            )
    )
      . distL @_ @s @t @m
      . (id &&& affineMatch @f @g f g)

  -- if the outer already fails, the new b is irrelevant; otherwise set inner-then-outer, reusing s
  affineSet @s @_ @b @t ((:.:) @m f@Objs f'@Objs) ((:.:) @n g'@Objs g@Objs) =
    withOb2 @_ @t @b $
      withOb2 @_ @m @b $
        ( (fst @t @b . snd @s @(t ** b))
            ||| (affineSet @f @g f g . tensorToProduct @s @n . second @s (affineSet @f' @g' f' g' . tensorToProduct @m @b))
        )
          . distL @_ @s @(t ** b) @(m ** b)
          . second @s (distR @_ @t @m @b)
          . (fst @s @b &&& first @b (affineMatch @f @g f g))
          . productToTensor @s @b

type AffineTraversal (s :: k) (t :: k) a b = Optic (Prostrong AffineTravFl) s t a b
type AffineTraversal' s a = AffineTraversal s s a a

-- | Match through any optic that can act as an affine traversal, in either encoding: returns the
-- focus (@'rgt'@) when it matches, or a reconstructed @t@ (@'lft'@) when it does not. This is the
-- 'AffineTraversal' eliminator, refining 'Proarrow.Optic.AffineFold.preview' (which forgets @t@).
-- Runs the optic at its witness pair ('ExOptic' 'AffineTravFl', via 'withLegs') and applies
-- 'affineMatch'.
matching
  :: forall {k} c (s :: k) (t :: k) a b
   . (Bicartesian k, (Ob a, Ob b) => c (ExOptic AffineTravFl a b))
  => Optic c s t a b -> s ~> (t || a)
matching o = withLegs @AffineTravFl o \ @p @q p q -> affineMatch @p @q p q
