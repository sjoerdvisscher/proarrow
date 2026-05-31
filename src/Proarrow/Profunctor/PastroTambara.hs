{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.PastroTambara where

import Prelude (($))

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..), composeActs, decomposeActs)
import Proarrow.Category.Monoidal.Optic (ExOptic (..))
import Proarrow.Category.Opposite (OPPOSITE (..))
import Proarrow.Core (CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj, (//), (:~>), type (+->), src, tgt, OB)
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Star (Star, pattern Star)
import Proarrow.Profunctor.Yoneda (Yo (..))
import Proarrow.Profunctor.Free (HasFree (..))
import Proarrow.Profunctor.Cofree (HasCofree (..))

type Pastro :: Kind -> j +-> k -> j +-> k
data Pastro m p a b where
  Pastro :: forall {m} (z :: m) x y p a b. (Ob z) => a ~> Act z x -> p x y -> Act z y ~> b -> Pastro m p a b

pastro :: forall {j} {k} m (p :: j +-> k). (Profunctor p, MonoidalAction m j, MonoidalAction m k) => p :~> Pastro m p
pastro p = Pastro @Unit (unitorInv @m) p (unitor @m) \\ p

unpastro :: forall {j} {k} m (p :: j +-> k). (Strong m p, MonoidalAction m j, MonoidalAction m k) => Pastro m p :~> p
unpastro (Pastro @z f p g) = dimap f g (act (obj @z) p)

instance (CategoryOf j, CategoryOf k) => Profunctor (Pastro m p :: j +-> k) where
  dimap l r (Pastro @z f p g) = Pastro @z (f . l) p (r . g)
  r \\ Pastro f _ g = r \\ f \\ g
instance (MonoidalAction m j, MonoidalAction m k, Profunctor p) => Strong m (Pastro m p :: j +-> k) where
  act @_ @b @x @y m (Pastro @z @x1 @y1 f p g) =
    withOb2 @m @b @z
      (Pastro @(b ** z) (composeActs @b @z @x1 (m `act` obj @x) f) p (decomposeActs @b @z @y1 g (obj @b `act` obj @y)))
      \\ m
      \\ f
      \\ g
      \\ p

instance (MonoidalAction m j, MonoidalAction m k) => HasFree (Strong m :: OB (j +-> k)) where
  type Free (Strong m) = Star (Pastro m)
  lift' n = Star (Prof pastro . n) \\ n
  retract' (Star n) = Prof unpastro  . n

instance Functor (Pastro m) where
  map (Prof n) = Prof \(Pastro @z f p g) -> Pastro @z f (n p) g
instance (MonoidalAction m j, MonoidalAction m k) => Promonad (Star (Pastro m) :: (j +-> k) +-> (j +-> k)) where
  id = Star (Prof pastro)
  Star n . Star m = Star (Prof unpastro . map n . m)

fromExOptic
  :: forall {j} {k} m (a :: k) (b :: j)
   . (MonoidalAction m j, MonoidalAction m k) => ExOptic m a b :~> (Pastro m (Yo a (OP b)) :: j +-> k)
fromExOptic (ExOptic @x f w g) = Pastro @x f (Yo id id) (g . (w `act` obj @b)) \\ w

type Tambara :: Kind -> j +-> k -> j +-> k
data Tambara m p a b where
  Tambara :: (Ob a, Ob b) => (forall (z :: m). (Ob z) => p (Act z a) (Act z b)) -> Tambara m p a b

tambara :: forall {j} {k} m (p :: j +-> k). (Strong m p, MonoidalAction m j, MonoidalAction m k) => p :~> Tambara m p
tambara p = Tambara (\ @z -> act (obj @z) p) \\ p

untambara
  :: forall {j} {k} m (p :: j +-> k). (Profunctor p, MonoidalAction m j, MonoidalAction m k) => Tambara m p :~> p
untambara (Tambara p) = dimap (unitorInv @m) (unitor @m) (p @Unit)

instance (MonoidalAction m j, MonoidalAction m k, Profunctor p) => Profunctor (Tambara m p :: j +-> k) where
  dimap l r (Tambara p) = Tambara (\ @z -> dimap (obj @z `act` l) (obj @z `act` r) (p @z)) \\ l \\ r
  r \\ Tambara{} = r
instance (MonoidalAction m j, MonoidalAction m k, Profunctor p) => Strong m (Tambara m p :: j +-> k) where
  act @a @b @x @y m (Tambara p) = m //
    withObAct @m @k @a @x $
      withObAct @m @j @b @y $
        Tambara \ @z ->
          withOb2 @m @z @b
            (dimap (multiplicatorInv @m @k @z @b @x . act (obj @z) (act m (obj @x))) (multiplicator @m @j @z @b @y) (p @(z ** b)))

instance (MonoidalAction m j, MonoidalAction m k) => HasCofree (Strong m :: OB (j +-> k)) where
  type Cofree (Strong m) = Star (Tambara m)
  lower' (Star n) = Prof untambara . n
  section' n = Star (map n . Prof tambara) \\ n

instance (MonoidalAction m j, MonoidalAction m k) => Functor (Tambara m :: (j +-> k) -> (j +-> k)) where
  map (Prof n) = Prof \(Tambara p) -> Tambara \ @z -> n (p @z)
instance (MonoidalAction m j, MonoidalAction m k) => Promonad (Costar (Tambara m) :: (j +-> k) +-> (j +-> k)) where
  id = Costar (Prof untambara)
  Costar n . Costar m = Costar (n . map m . Prof tambara)

-- | @Pastro m@ ⊣ @Tambara m@
instance (MonoidalAction m j, MonoidalAction m k) => Corepresentable (Star (Tambara m) :: (j +-> k) +-> (j +-> k)) where
  type Star (Tambara m) %% p = Pastro m p
  coindex (Star (Prof n)) = Prof \(Pastro @z f p g) -> case n p of Tambara q -> dimap f g (q @z)
  cotabulate (Prof n) = Star (Prof \p -> p // Tambara \ @z -> n (Pastro @z (obj @z `act` src p) p (obj @z `act` tgt p)))
  corepMap = map
