{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The __affine fold__: a fold that sees at most one focus, @s '~>' (a '||' 'TerminalObject')@
-- ('AffineFoldRes' \/ 'previewP'). Every 'Proarrow.Optic.Getter.Getter' and
-- 'Proarrow.Optic.AffineTraversal.AffineTraversal' is one, and it subtypes to
-- 'Proarrow.Optic.Fold.Fold'. Like all read-only flavors it has no builder of its own
-- ('Proarrow.Optic.convert' a stronger optic); its canonical eliminator is 'preview' \/ '(^?)',
-- via the generic 'ExOptic' carrier.
module Proarrow.Optic.AffineFold where

import Data.Kind (Type)
import Prelude (Maybe (..), const, either)

import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Distributive (Bicartesian)
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, Product, snd)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Optic (ExOptic, FLAVOR, Optic, Prostrong (..), SubFlavor (..), withLegs)
import Proarrow.Optic.Fold (FoldRes)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | An affine fold is a fold that can see at most one @a@ -- 0-or-1, never 0-or-many. A getter
-- is an affine fold that always succeeds; an affine traversal is one that additionally knows how
-- to reconstruct a @t@ when it fails to match.
type AffineFoldRes :: forall {j} {k}. FLAVOR j k
class (FoldRes p q) => AffineFoldRes (p :: k +-> k) (q :: j +-> j) where
  previewP :: (Bicartesian k) => p s a -> s ~> (a || TerminalObject)

instance (HasBinaryProducts k, Ob (s :: k)) => AffineFoldRes (Rep (Product s)) (Corep (Product s)) where
  previewP @_ @a (Rep p) = lft @k @a @TerminalObject . snd @k @s @a . p
instance (CategoryOf k, CategoryOf j) => AffineFoldRes (Id :: k +-> k) (Id :: j +-> j) where
  previewP @_ @a (Id sa) = lft @k @a @TerminalObject . sa \\ sa
instance (CategoryOf k, CategoryOf j) => AffineFoldRes (Id :: k +-> k) (TerminalProfunctor :: j +-> j) where
  previewP @_ @a (Id sa) = lft @k @a @TerminalObject . sa \\ sa
instance (AffineFoldRes f g, AffineFoldRes f' g') => AffineFoldRes (f :.: f') (g' :.: g) where
  previewP @_ @a (f :.: f') = (previewP @f' @g' f' ||| rgt @_ @a @TerminalObject) . previewP @f @g f \\ f'
instance (HasCoproducts k, Ob t) => AffineFoldRes (Corep (Coproduct t) :: k +-> k) (Rep (Coproduct t)) where
  previewP @_ @a (Corep f) = lft @k @a @TerminalObject . f . rgt @k @t \\ f
instance (CopyDiscard k, HasCoproducts k, Ob t) => AffineFoldRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  previewP @_ @a (Rep p) = ((rgt @k @a @TerminalObject . terminate @k @t) ||| lft @k @a @TerminalObject) . p

instance SubFlavor AffineFoldRes FoldRes where subFlavor r = r

type AffineFold (s :: k) (t :: j) a b = Optic (Prostrong AffineFoldRes) s t a b

-- | Preview through any optic that can act as an affine fold, in either encoding: run it at its
-- witness pair ('ExOptic' 'AffineFoldRes', via 'withLegs') and apply 'previewP'.
preview
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (Bicartesian k, CategoryOf j, (Ob a, Ob b) => c (ExOptic AffineFoldRes a b))
  => Optic c s t a b -> s ~> (a || TerminalObject)
preview o = withLegs @AffineFoldRes o \ @p @q p _ -> previewP @p @q p

infixl 8 ^?

-- | Preview the focus of a concrete, @Type@-level optic (a getter that might not match).
(^?) :: forall s (t :: Type) a b c. (c (ExOptic AffineFoldRes a b)) => s -> Optic c s t a b -> Maybe a
s ^? l = either Just (const Nothing) (preview l s)
