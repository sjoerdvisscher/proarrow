{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Optic.AffineTraversal where

import Prelude (($))

import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Distributive (Bicartesian, Distributive (..))
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasBinaryCoproducts (..), HasCoproducts, left)
import Proarrow.Core (CategoryOf (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), Product, TensorIsProduct, first, second)
import Proarrow.Object (pattern Objs)
import Proarrow.Optic (CompactFlavor, FLAVOR, Optic, Prostrong, SubFlavor (..))
import Proarrow.Optic.AffineFold (AffineFoldRes)
import Proarrow.Optic.Fold (FoldRes)
import Proarrow.Optic.Setter (SetterRes)
import Proarrow.Optic.Traversal (TravRes)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | 'distL'/'distR' are stated in terms of @**@, which is only /equal/ to '&&' under
-- 'Proarrow.Limit.BinaryProduct.Cartesian' rather than reducing to it, and that equality doesn't propagate through the
-- non-injective '||' automatically. Forcing 'TensorIsProduct' to be solved at each component
-- (rather than relying on the quantified constraint 'Proarrow.Limit.BinaryProduct.Cartesian' provides to fire implicitly)
-- materializes the equalities as givens so they rewrite inside '||' too.
distLP
  :: forall k (a :: k) b c
   . (Distributive k, Ob a, Ob b, Ob c, TensorIsProduct a (b || c), TensorIsProduct a b, TensorIsProduct a c)
  => (a && (b || c)) ~> (a && b || a && c)
distLP = distL @k @a @b @c

distRP
  :: forall k (a :: k) b c
   . (Distributive k, Ob a, Ob b, Ob c, TensorIsProduct (a || b) c, TensorIsProduct a c, TensorIsProduct b c)
  => ((a || b) && c) ~> (a && c || b && c)
distRP = distR @k @a @b @c

type AffineTravRes :: forall {k}. FLAVOR k k
class (TravRes p q, AffineFoldRes p q) => AffineTravRes (p :: k +-> k) (q :: k +-> k) where
  affineMatch :: (Bicartesian k) => p (s :: k) a -> q b t -> s ~> (t || a)
  affineSet :: (Bicartesian k) => p (s :: k) a -> q b t -> (s && b) ~> t
instance (HasBinaryProducts k, Ob (s :: k)) => AffineTravRes (Rep (Product s)) (Corep (Product s)) where
  -- a lens always matches
  affineMatch @_ @a @_ @t (Rep p) q = rgt @k @t @a . snd @k @s @a . p \\ p \\ q
  affineSet @_ @a @b (Rep p) (Corep q) = q . first @b (fst @k @s @a . p)
instance (CopyDiscard k, HasCoproducts k, Ob t) => AffineTravRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  affineMatch @_ @a @b (Rep p) (Corep q) = left @a (q . lft @k @t @b) . p

  -- a prism's set never needs the original value, it just reviews
  affineSet @s @_ @b (Rep p) (Corep q) = q . rgt @k @t @b . snd @k @s @b \\ p
instance (CategoryOf k) => AffineTravRes (Id :: k +-> k) (Id :: k +-> k) where
  affineMatch @_ @a @_ @t (Id sa) bt = rgt @k @t @a . sa \\ sa \\ bt
  affineSet @s @_ @b sa (Id bt) = bt . snd @k @s @b \\ sa \\ bt
instance (AffineTravRes f g, AffineTravRes f' g') => AffineTravRes (f :.: f') (g' :.: g) where
  -- match the outer; on failure of the inner, reconstruct via the outer's own setter, reusing s
  affineMatch @s @a @_ @t ((:.:) @m f@Objs f'@Objs) ((:.:) @n g'@Objs g@Objs) =
    ( (lft @_ @t @a . snd @_ @s @t)
        ||| ( ((lft @_ @t @a . affineSet @f @g f g) ||| (rgt @_ @t @a . snd @_ @s @a))
                . distLP @_ @s @n @a
                . second @s (affineMatch @f' @g' f' g')
            )
    )
      . distLP @_ @s @t @m
      . (id &&& affineMatch @f @g f g)

  -- if the outer already fails, the new b is irrelevant; otherwise set inner-then-outer, reusing s
  affineSet @s @_ @b @t ((:.:) @m f@Objs f'@Objs) ((:.:) g'@Objs g@Objs) =
    withObProd @_ @t @b $
      withObProd @_ @m @b $
        ( (fst @_ @t @b . snd @_ @s @(t && b))
            ||| (affineSet @f @g f g . second @s (affineSet @f' @g' f' g'))
        )
          . distLP @_ @s @(t && b) @(m && b)
          . second @s (distRP @_ @t @m @b)
          . (fst @_ @s @b &&& first @b (affineMatch @f @g f g))

instance SubFlavor AffineTravRes TravRes where subFlavor r = r
instance SubFlavor AffineTravRes SetterRes where subFlavor r = r
instance SubFlavor AffineTravRes AffineFoldRes where subFlavor r = r
instance SubFlavor AffineTravRes FoldRes where subFlavor r = r

instance CompactFlavor AffineTravRes

type AffineTraversal (s :: k) (t :: k) a b = Optic (Prostrong AffineTravRes) s t a b
