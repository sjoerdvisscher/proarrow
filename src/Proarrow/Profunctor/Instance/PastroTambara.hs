{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Instance.PastroTambara where

import Prelude (($))

import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Monoidal.Action (Act, MonoidalAction (..), actHom, composeActs, decomposeActs)
import Proarrow.Category.Monoidal.Optic (ExOptic (..))
import Proarrow.Category.Monoidal.Strength (Strong (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), obj, (//), (:~>), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Cofree (HasCofree (..), cofreeComp)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Free (HasFree (..), freeComp)
import Proarrow.Profunctor.Instance.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))
import Proarrow.Profunctor.Representable (repObj, withObRep)

type Pastro :: (m, k) +-> k -> k +-> k -> k +-> k
data Pastro t p a b where
  Pastro
    :: forall {m} {k} {t :: (m, k) +-> k} (z :: m) x y p a b
     . (Ob z) => a ~> Act t z x -> p x y -> Act t z y ~> b -> Pastro t p a b

pastro :: forall {k} t (p :: k +-> k). (Profunctor p, MonoidalAction t) => p :~> Pastro t p
pastro p = Pastro @Unit (unitorInv @t) p (unitor @t) \\ p

unpastro :: forall {k} t (p :: k +-> k). (Strong t p, MonoidalAction t) => Pastro t p :~> p
unpastro (Pastro @z f p g) = dimap f g (act @t @p @z p)

instance (CategoryOf k) => Profunctor (Pastro t p :: k +-> k) where
  dimap l r (Pastro @z f p g) = Pastro @z (f . l) p (r . g)
  r \\ Pastro f _ g = r \\ f \\ g
instance (MonoidalAction t, Profunctor p) => Strong t (Pastro t p :: k +-> k) where
  act @a @x @y (Pastro @z @x1 @y1 f p g) =
    withOb2 @_ @a @z
      (Pastro @(a ** z) (composeActs @t @a @z @x1 (repObj @t @'(a, x)) f) p (decomposeActs @t @a @z @y1 g (repObj @t @'(a, y))))
      \\ f
      \\ g
      \\ p

instance (MonoidalAction t) => HasFree (Strong t :: OB (k +-> k)) where
  type Free (Strong t) p = Pastro t p
  lift = Prof pastro
  foldMap n = Prof unpastro . map n

instance Functor (Pastro t) where
  map (Prof n) = Prof \(Pastro @z f p g) -> Pastro @z f (n p) g
instance (MonoidalAction t) => Promonad (Star (Pastro t) :: (k +-> k) +-> (k +-> k)) where
  id = Star (Prof pastro)
  Star n . Star m = Star (freeComp @(Strong t) n m)

fromWeightedOptic
  :: forall {k} t (a :: k) (b :: k)
   . (MonoidalAction t) => ExOptic t a b :~> (Pastro t (Yo a (OP b)) :: k +-> k)
fromWeightedOptic (ExOptic @x f g) = Pastro @x f (Yo id id) g

type Tambara :: (m, k) +-> k -> k +-> k -> k +-> k
data Tambara t p a b where
  Tambara :: (Ob a, Ob b) => (forall (z :: m). (Ob z) => p (Act t z a) (Act t z b)) -> Tambara t p a b

tambara :: forall {k} t (p :: k +-> k). (Strong t p, MonoidalAction t) => p :~> Tambara t p
tambara p = Tambara (\ @z -> act @t @p @z p) \\ p

untambara
  :: forall {k} t (p :: k +-> k). (Profunctor p, MonoidalAction t) => Tambara t p :~> p
untambara (Tambara p) = dimap (unitorInv @t) (unitor @t) (p @Unit)

instance (MonoidalAction t, Profunctor p) => Profunctor (Tambara t p :: k +-> k) where
  dimap l r (Tambara p) = Tambara (\ @z -> dimap (actHom @t (obj @z) l) (actHom @t (obj @z) r) (p @z)) \\ l \\ r
  r \\ Tambara{} = r
instance (MonoidalAction t, Profunctor p) => Strong t (Tambara t p :: k +-> k) where
  act @a @x @y (Tambara p) = withObRep @t @'(a, x) $ withObRep @t @'(a, y) $ Tambara \ @z ->
    withOb2 @_ @z @a $
      dimap (multiplicatorInv @t @z @a @x) (multiplicator @t @z @a @y) (p @(z ** a))

instance (MonoidalAction t) => HasCofree (Strong t :: OB (k +-> k)) where
  type Cofree (Strong t) p = Tambara t p
  lower = Prof untambara
  unfoldMap n = map n . Prof tambara

instance (MonoidalAction t) => Functor (Tambara t :: (k +-> k) -> (k +-> k)) where
  map (Prof n) = Prof \(Tambara p) -> Tambara \ @z -> n (p @z)
instance (MonoidalAction t) => Promonad (Costar (Tambara t) :: (k +-> k) +-> (k +-> k)) where
  id = Costar (Prof untambara)
  Costar n . Costar m = Costar (cofreeComp @(Strong t) n m)

-- | @Pastro t@ ⊣ @Tambara t@
instance (MonoidalAction t) => Corepresentable (Star (Tambara t) :: (k +-> k) +-> (k +-> k)) where
  type Star (Tambara t) %% p = Pastro t p
  coindex (Star (Prof n)) = Prof \(Pastro @z f p g) -> case n p of Tambara q -> dimap f g (q @z)
  cotabulate (Prof n) = Star (Prof \ @a @b p -> p // Tambara \ @z -> n (Pastro @z (repObj @t @'(z, a)) p (repObj @t @'(z, b))))
  corepMap = map
