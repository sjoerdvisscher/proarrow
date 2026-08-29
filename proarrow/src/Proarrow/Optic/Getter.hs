{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Optic.Getter where

import Data.Kind (Type)

import Proarrow.Colimit.BinaryCoproduct (Coproduct, HasCoproducts, rgt)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, Product, snd)
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
import Proarrow.Optic.Fold (FoldRes)
import Proarrow.Profunctor.Corepresentable (Corep (..), corep)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (Rep (..), rep)

type GetterRes :: forall {j} {k}. FLAVOR j k
class (AffineFoldRes p q) => GetterRes (p :: k +-> k) (q :: j +-> j) where
  getP :: p s a -> s ~> a
instance (HasBinaryProducts k, Ob (s :: k)) => GetterRes (Rep (Product s)) (Corep (Product s)) where
  getP @_ @a (Rep p) = snd @k @s @a . p
instance (CategoryOf k, CategoryOf j) => GetterRes (Id :: k +-> k) (Id :: j +-> j) where
  getP = unId
instance (CategoryOf k, CategoryOf j) => GetterRes (Id :: k +-> k) (TerminalProfunctor :: j +-> j) where
  getP = unId
instance (GetterRes f g, GetterRes f' g') => GetterRes (f :.: f') (g' :.: g) where
  getP (f :.: f') = getP @f' @g' f' . getP @f @g f
instance (HasCoproducts k, Ob t) => GetterRes (Corep (Coproduct t) :: k +-> k) (Rep (Coproduct t)) where
  getP (Corep f) = f . rgt @k @t

instance CompactFlavor GetterRes
instance CompactFlavor (Flip GetterRes)

instance SubFlavor GetterRes AffineFoldRes where subFlavor r = r
instance SubFlavor GetterRes FoldRes where subFlavor r = r

type Getter (s :: k) (t :: j) a b = Optic (Prostrong GetterRes) s t a b

-- | Any flavor whose optics can view has strength for the viewing carrier @'Rep' ('Constant' a)@.
-- This is the bridge that lets the encoding-agnostic 'view' below consume 'Prostrong'-flavored
-- optics; profunctor-class-flavored optics discharge the same @c ('Rep' ('Constant' a))@
-- constraint through the carrier's ordinary class instances instead.
instance
  (CategoryOf j, CategoryOf k, Ob (a :: k), SubFlavor w GetterRes)
  => Prostrong (w :: FLAVOR j k) (Rep (Constant a) :: j +-> k)
  where
  proact @f @g (f :.: Rep h :.: g) = subFlavor @w @GetterRes @f @g (Rep (h . getP @f @g f)) \\ g

-- | The reviewing dual of the bridge above, over the carrier @'Corep' ('Constant' b)@.
instance
  (CategoryOf j, CategoryOf k, Ob (b :: j), SubFlavor w (Flip GetterRes))
  => Prostrong (w :: FLAVOR j k) (Corep (Constant b) :: j +-> k)
  where
  proact @f @g (f :.: Corep h :.: g) = subFlavor @w @(Flip GetterRes) @f @g (Corep (getP @g @f g . h)) \\ f

-- | View through any optic that can act as a getter, in either encoding: a 'Prostrong'-flavored
-- optic needs @'SubFlavor' w 'GetterRes'@ (discharged by the bridge instance above), a
-- profunctor-class-flavored optic needs its class to hold for the carrier.
view
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, (Ob a) => c (Rep (Constant a)))
  => Optic c s t a b -> s ~> a
view (Optic l) = unOptic (rep @(Constant a)) l id

infixl 8 ^.

-- | View the focus of a concrete, @Type@-level optic.
(^.) :: (c (Rep (Constant a))) => s -> Optic c (s :: Type) (t :: Type) a b -> a
s ^. l = view l s

to :: forall {k} {j} (s :: k) (t :: j) a b. (CategoryOf k, CategoryOf j, Ob b, Ob t) => (s ~> a) -> Getter s t a b
to sa = ex2prof (ExProstrong @Id @TerminalProfunctor (Id sa :.: ExIso id id :.: TerminalProfunctor)) \\ sa

type Review (s :: k) (t :: j) a b = Optic (Prostrong (Flip GetterRes)) s t a b

-- | Review through any optic that can act as a review, in either encoding.
review
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, (Ob b) => c (Corep (Constant b)))
  => Optic c s t a b -> b ~> t
review (Optic l) = unOptic (corep @(Constant b)) l id

infixr 8 #

-- | Review through a concrete, @Type@-level optic.
(#) :: (c (Corep (Constant b))) => Optic c (s :: Type) (t :: Type) a b -> b -> t
(#) = review

unto :: forall {k} {j} (s :: k) (t :: j) a b. (CategoryOf k, CategoryOf j, Ob s, Ob a) => (b ~> t) -> Review s t a b
unto bt = ex2prof (ExProstrong @TerminalProfunctor @Id (TerminalProfunctor :.: ExIso id id :.: Id bt)) \\ bt
