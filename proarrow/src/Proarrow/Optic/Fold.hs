{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Optic.Fold where

import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..), UnOp)
import Proarrow.Category.Monoidal.Distributive
  ( Bicartesian
  , Cotraversable (..)
  , Traversable (..)
  , corepTraverse
  , repTraverse
  )
import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasCoproducts, rgt, (|||))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, Product, snd)
import Proarrow.Limit.Terminal (HasTerminalObject (..), Semicartesian)
import Proarrow.Monoid (Comonoid, Monoid (..))
import Proarrow.Optic
  ( CompactFlavor
  , FLAVOR
  , OpConstraint
  , Optic
  , Optic_ (..)
  , Prostrong (..)
  , SubFlavor (..)
  , opOptic
  )
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), RepCostar, Representable (..))

-- | A fold is a getter or traversal that forgets everything except the ability to reduce the
-- @a@'s it can see into any monoid object of @k@ -- it can never reconstruct a @t@.
type FoldRes :: forall {j} {k}. FLAVOR j k
class (Profunctor p, Profunctor q) => FoldRes (p :: k +-> k) (q :: j +-> j) where
  foldMapP :: (Monoid m) => p s a -> (a ~> m) -> (s ~> m)

instance (HasBinaryProducts k, Ob (s :: k)) => FoldRes (Rep (Product s)) (Corep (Product s)) where
  foldMapP (Rep p) am = am . snd @k @s . p
instance (CategoryOf k, CategoryOf j) => FoldRes (Id :: k +-> k) (Id :: j +-> j) where
  foldMapP (Id sa) am = am . sa
instance (CategoryOf k, CategoryOf j) => FoldRes (Id :: k +-> k) (TerminalProfunctor :: j +-> j) where
  foldMapP (Id sa) am = am . sa
instance (FoldRes f g, FoldRes f' g') => FoldRes (f :.: f') (g' :.: g) where
  foldMapP (f :.: f') = foldMapP @f @g f . foldMapP @f' @g' f'
instance (Bicartesian k, Traversable t, Representable t) => FoldRes (t :: k +-> k) (RepCostar t) where
  foldMapP @m @_ @a l am = (case repTraverse @t @(Rep (Constant m)) (Rep @a am) of Rep sm -> sm . index l) \\ am

-- | The corepresentable-cotraversable witness folds by cotraversing at the fold profunctor @'Rep' ('Constant' m)@
-- -- the residual shape is simply discarded.
instance (Bicartesian k, Cotraversable t, Corepresentable t) => FoldRes (CorepStar t) (t :: k +-> k) where
  foldMapP @m @_ @a (CorepStar l) am = (case corepTraverse @t @(Rep (Constant m)) (Rep @a am) of Rep sm -> sm . l) \\ am

instance (HasCoproducts k, Ob t) => FoldRes (Corep (Coproduct t) :: k +-> k) (Rep (Coproduct t)) where
  foldMapP (Corep f) am = am . f . rgt @k @t
instance (Semicartesian k, HasCoproducts k, Ob t) => FoldRes (Rep (Coproduct t) :: k +-> k) (Corep (Coproduct t)) where
  foldMapP @m (Rep p) am = (mempty @m . terminate @k @t ||| am) . p

instance CompactFlavor FoldRes

type Fold (s :: k) (t :: j) a b = Optic (Prostrong FoldRes) s t a b

-- | The carrier profunctor for 'foldMapOf': a generalized @s -> m@ (the @Forget@ of the
-- @optics@ library).
type Forget :: forall {j} {k}. k -> j +-> k
data Forget (m :: k) (s :: k) (t :: j) where
  Forget :: (Ob t) => {unForget :: s ~> m} -> Forget m s t

instance (CategoryOf j, CategoryOf k, Ob (m :: k)) => Profunctor (Forget m :: j +-> k) where
  dimap l r (Forget f) = Forget (f . l) \\ r
  r \\ Forget f = r \\ f

-- | Any flavor whose optics can fold has strength for the 'Forget' carrier.
instance (CategoryOf j, Monoid m, SubFlavor w FoldRes) => Prostrong (w :: FLAVOR j k) (Forget m :: j +-> k) where
  proact @f @g (f :.: Forget h :.: g) = subFlavor @w @FoldRes @f @g (Forget (foldMapP @f @g f h)) \\ g

-- | Fold through any optic that can act as a fold, in either encoding.
foldMapOf
  :: forall {j} {k} c m (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, Ob m, c (Forget m))
  => Optic c s t a b -> (a ~> m) -> (s ~> m)
foldMapOf (Optic l) am = unForget (l @(Forget m) (Forget am))

-- | The genuine unfold: build @t@ from a 'Comonoid' seed @cm@ through the @b@-foci. It is
-- 'foldMapOf' run in @'OPPOSITE' k@, where 'Monoid' becomes 'Comonoid' and consumption becomes
-- construction. (Inhabitable once the flavor's 'Prostrong' transports through 'OP'.)
unfold
  :: forall {k} c (cm :: k) (s :: k) t a b
   . (Comonoid cm, Ob cm, forall p. (c p) => c (Op (UnOp p)), c (Forget (OP cm)))
  => Optic (OpConstraint c) s t a b -> (cm ~> b) -> (cm ~> t)
unfold o cb = unOp (foldMapOf @c (opOptic o) (Op cb))
