{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Optic.AffineFold where

import Data.Kind (Type)
import Prelude (Maybe (..), const, either)

import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Category.Monoidal.Distributive (Bicartesian)
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, Product, snd)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Optic (CompactFlavor, FLAVOR, Optic, Optic_ (..), Prostrong (..), SubFlavor (..))
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

instance CompactFlavor AffineFoldRes

instance SubFlavor AffineFoldRes FoldRes where subFlavor r = r

type AffineFold (s :: k) (t :: j) a b = Optic (Prostrong AffineFoldRes) s t a b

-- | The carrier profunctor for 'preview': a generalized @s -> Maybe a@.
type PreviewP :: forall {j} {k}. k -> j +-> k
data PreviewP (a :: k) (s :: k) (t :: j) where
  PreviewP :: (Ob t) => {unPreviewP :: s ~> (a || TerminalObject)} -> PreviewP a s t

instance (Bicartesian k, CategoryOf j, Ob (a :: k)) => Profunctor (PreviewP a :: j +-> k) where
  dimap l r (PreviewP f) = PreviewP (f . l) \\ r
  r \\ PreviewP f = r \\ f

-- | Any flavor whose optics can preview has strength for the 'PreviewP' carrier.
instance
  (Bicartesian k, CategoryOf j, Ob (a :: k), SubFlavor w AffineFoldRes)
  => Prostrong (w :: FLAVOR j k) (PreviewP a :: j +-> k)
  where
  proact @f @g (f :.: PreviewP h :.: g) =
    subFlavor @w @AffineFoldRes @f @g (PreviewP ((h ||| rgt @k @a @TerminalObject) . previewP @f @g f)) \\ g

-- | Preview through any optic that can act as an affine fold, in either encoding.
preview
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (Bicartesian k, CategoryOf j, c (PreviewP a))
  => Optic c s t a b -> s ~> (a || TerminalObject)
preview (Optic l) = unPreviewP (l @(PreviewP a) (PreviewP (lft @k @a @TerminalObject)))

infixl 8 ^?

-- | Preview the focus of a concrete, @Type@-level optic (a getter that might not match).
(^?) :: forall s (t :: Type) a b c. (c (PreviewP a)) => s -> Optic c s t a b -> Maybe a
s ^? l = either Just (const Nothing) (preview l s)
