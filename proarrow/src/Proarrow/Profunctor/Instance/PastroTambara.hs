{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | 'Pastro' and 'Tambara' are the free and cofree 'Prostrong' profunctors for an optic flavor @w@ (the
-- 'HasFree' and 'HasCofree' instances for @'Prostrong' w@): @Pastro w r@ sandwiches @r@ between an
-- existential witness pair, while @Tambara w r@ provides strength against every witness pair at once.
module Proarrow.Profunctor.Instance.PastroTambara where

import Prelude (($))

import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), src, tgt, (//), (:~>), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Optic (ExOptic (..), FLAVOR, Flavor, Prostrong (..))
import Proarrow.Profunctor.Cofree (HasCofree (..), cofreeComp)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Free (HasFree (..), freeComp)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Costar (Costar, pattern Costar)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Ran (Ran (..), runRan, type (|>))
import Proarrow.Profunctor.Instance.Rift (Rift (..), runRift, type (<|))
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

-- | The free 'Prostrong' profunctor for the flavor @w@: the profunctor @r@ sandwiched between an
-- existential @w@-witness pair.
type Pastro :: FLAVOR j k -> j +-> k -> j +-> k
data Pastro w r a b where
  Pastro
    :: forall {k} {j} (p :: k +-> k) (q :: j +-> j) w r a b
     . (w p q, Profunctor p, Profunctor q) => (p :.: r :.: q) a b -> Pastro w r a b

pastro :: forall {j} {k} (w :: FLAVOR j k) (p :: j +-> k). (Profunctor p, Flavor w) => p :~> Pastro w p
pastro p = Pastro (Id id :.: p :.: Id id) \\ p

unpastro :: forall {j} {k} (w :: FLAVOR j k) (p :: j +-> k). (Prostrong w p) => Pastro w p :~> p
unpastro (Pastro fpg) = proact @w fpg

instance (CategoryOf j, CategoryOf k, Profunctor p) => Profunctor (Pastro t p :: j +-> k) where
  dimap l r (Pastro fpg) = Pastro (dimap l r fpg)
  r \\ Pastro fpg = r \\ fpg
instance (Flavor w, Profunctor p) => Prostrong w (Pastro w p :: j +-> k) where
  proact (p :.: Pastro (p' :.: r :.: q') :.: q) = Pastro ((p :.: p') :.: r :.: (q' :.: q))

instance (Flavor w) => HasFree (Prostrong w :: OB (j +-> k)) where
  type Free (Prostrong w) p = Pastro w p
  lift = Prof pastro
  foldMap n = Prof unpastro . map n

instance Functor (Pastro t) where
  map (Prof n) = Prof \(Pastro (f :.: p :.: g)) -> Pastro (f :.: n p :.: g)
instance (Flavor w) => Promonad (Star (Pastro w) :: (j +-> k) +-> (j +-> k)) where
  id = Star (Prof pastro)
  Star n . Star m = Star (freeComp @(Prostrong w) n m)

fromExOptic
  :: forall {j} {k} w (a :: k) (b :: j)
   . (CategoryOf j, CategoryOf k) => ExOptic w a b :~> (Pastro w (Yo a (OP b)) :: j +-> k)
fromExOptic (ExOptic f g) = Pastro (f :.: Yo (tgt f) (src g) :.: g)

-- | The cofree 'Prostrong' profunctor for the flavor @w@: strength against every @w@-witness pair
-- at once.
type Tambara :: FLAVOR j k -> j +-> k -> j +-> k
data Tambara w r a b where
  Tambara
    :: (Ob a, Ob b)
    => (forall (p :: k +-> k) (q :: j +-> j). (w p q, Profunctor p, Profunctor q) => (q |> r <| p) a b)
    -> Tambara w r a b

mkTambara
  :: (Ob a, Ob b)
  => (forall (p :: k +-> k) (q :: j +-> j) x y. (w p q, Profunctor p, Profunctor q) => p x a -> q b y -> r x y)
  -> Tambara w r a b
mkTambara f = Tambara (Rift \p -> p // Ran \q -> f p q)

runTambara :: (w p q, Profunctor p, Profunctor q) => ((Ob a) => p x a) -> ((Ob b) => q b y) -> Tambara w r a b -> r x y
runTambara p q (Tambara qrp) = runRan q $ runRift p qrp

tambara :: forall {j} {k} w (p :: j +-> k). (Prostrong w p) => p :~> Tambara w p
tambara r = mkTambara (\p q -> proact @w (p :.: r :.: q)) \\ r

untambara
  :: forall {j} {k} w (p :: j +-> k). (Profunctor p, Flavor w) => Tambara w p :~> p
untambara = runTambara @w @Id @Id (Id id) (Id id)

instance (Profunctor p) => Profunctor (Tambara w p :: j +-> k) where
  dimap l r (Tambara n) = Tambara (dimap l r n) \\ l \\ r
  r \\ Tambara{} = r

instance (Flavor w, Profunctor p) => Prostrong w (Tambara w p :: j +-> k) where
  proact (p :.: n :.: q) = mkTambara (\p' q' -> runTambara (p' :.: p) (q :.: q') n) \\ p \\ q

instance (Flavor w) => HasCofree (Prostrong w :: OB (j +-> k)) where
  type Cofree (Prostrong w) p = Tambara w p
  lower = Prof untambara
  unfoldMap n = map n . Prof tambara

instance Functor (Tambara w :: (j +-> k) -> (j +-> k)) where
  map (Prof n) = Prof \t -> t // mkTambara \p q -> n (runTambara p q t)
instance (Flavor w) => Promonad (Costar (Tambara w) :: (j +-> k) +-> (j +-> k)) where
  id = Costar (Prof untambara)
  Costar n . Costar m = Costar (cofreeComp @(Prostrong w) n m)

-- | @Pastro t@ ⊣ @Tambara t@
instance Corepresentable (Star (Tambara w) :: (j +-> k) +-> (j +-> k)) where
  type Star (Tambara w) %% p = Pastro w p
  coindex (Star (Prof n)) = Prof \(Pastro @p @q (p :.: r :.: q)) -> case n r of m -> runTambara @w @p @q p q m
  corepUniv = Star (Prof \r -> r // mkTambara \p q -> Pastro (p :.: r :.: q))
