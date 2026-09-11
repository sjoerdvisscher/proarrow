{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The __getter__ and its mirror the __review__: the one-leg optics @s '~>' a@ ('GetterFl' \/
-- 'getP') and @b '~>' t@ (its 'Flip'). A getter is an affine fold that always succeeds; a review
-- is what remains of a prism's build leg. Build them from a single morphism with 'to' \/ 'unto',
-- and eliminate with 'view' \/ '(^.)' and 'review' \/ '(#)', via the generic 'ExOptic' carrier.
module Proarrow.Optic.Getter where

import Data.Kind (Type)

import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasCoproducts, rgt)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, Product, snd)
import Proarrow.Optic
  ( ExOptic
  , FLAVOR
  , Flip
  , Optic
  , Prostrong (..)
  , SubFlavor (..)
  , legs2prof
  , withLegs
  )
import Proarrow.Optic.AffineFold (AffineFoldFl)
import Proarrow.Optic.Fold (FoldFl)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (Rep (..))

type GetterFl :: forall {j} {k}. FLAVOR j k
class (AffineFoldFl p q) => GetterFl (p :: k +-> k) (q :: j +-> j) where
  getP :: p s a -> s ~> a
instance (HasBinaryProducts k, Ob (s :: k)) => GetterFl (Rep (Product s)) (Corep (Product s)) where
  getP @_ @a (Rep p) = snd @k @s @a . p
instance (CategoryOf k, CategoryOf j) => GetterFl (Id :: k +-> k) (Id :: j +-> j) where
  getP = unId
instance (CategoryOf k, CategoryOf j) => GetterFl (Id :: k +-> k) (TerminalProfunctor :: j +-> j) where
  getP = unId
instance (GetterFl f g, GetterFl f' g') => GetterFl (f :.: f') (g' :.: g) where
  getP (f :.: f') = getP @f' @g' f' . getP @f @g f
instance (HasCoproducts k, Ob t) => GetterFl (Corep (Coproduct t) :: k +-> k) (Rep (Coproduct t)) where
  getP (Corep f) = f . rgt @k @t

instance SubFlavor GetterFl AffineFoldFl where subFlavor r = r
instance SubFlavor GetterFl FoldFl where subFlavor r = r

type Getter (s :: k) (t :: j) a b = Optic (Prostrong GetterFl) s t a b

-- | View through any optic that can act as a getter, in either encoding: run it at its witness
-- pair ('ExOptic' 'GetterFl', via 'withLegs') and read the get leg off with 'getP'.
view
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, (Ob a, Ob b) => c (ExOptic GetterFl a b))
  => Optic c s t a b -> s ~> a
view o = withLegs @GetterFl o \ @p @q p _ -> getP @p @q p

infixl 8 ^.

-- | View the focus of a concrete, @Type@-level optic.
(^.) :: (c (ExOptic GetterFl a b)) => s -> Optic c (s :: Type) (t :: Type) a b -> a
s ^. l = view l s

to :: forall {k} {j} (s :: k) (t :: j) a b. (CategoryOf k, CategoryOf j, Ob b, Ob t) => (s ~> a) -> Getter s t a b
to sa = legs2prof @GetterFl (Id sa) TerminalProfunctor \\ sa

type Review (s :: k) (t :: j) a b = Optic (Prostrong (Flip GetterFl)) s t a b

-- | Review through any optic that can act as a review, in either encoding: 'getP' on the flipped
-- witness pair.
review
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, (Ob a, Ob b) => c (ExOptic (Flip GetterFl) a b))
  => Optic c s t a b -> b ~> t
review o = withLegs @(Flip GetterFl) o \ @p @q _ q -> getP @q @p q

infixr 8 #

-- | Review through a concrete, @Type@-level optic.
(#) :: (c (ExOptic (Flip GetterFl) a b)) => Optic c (s :: Type) (t :: Type) a b -> b -> t
(#) = review

unto :: forall {k} {j} (s :: k) (t :: j) a b. (CategoryOf k, CategoryOf j, Ob s, Ob a) => (b ~> t) -> Review s t a b
unto bt = legs2prof @(Flip GetterFl) TerminalProfunctor (Id bt) \\ bt
