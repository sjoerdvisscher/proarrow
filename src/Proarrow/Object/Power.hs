{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Object.Power where

import Data.Kind (Type)
import Prelude (($), type (~))

import Proarrow.Category.Enriched (Enriched, EnrichedProfunctor (..), HomObj, comp)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (leftUnitorInvWith)
import Proarrow.Core (CategoryOf (..), Ob, Profunctor (..), Promonad (..), (//), type (+->))
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Terminal (TerminalObject, terminate)

-- | Categories powered over @v@.
class (Enriched v k, Closed v) => Powered v k where
  type (a :: k) ^ (n :: v) :: k
  withObPower :: (Ob (a :: k), Ob (n :: v)) => ((Ob (a ^ n)) => r) -> r
  power :: (Ob (a :: k), Ob b) => (n ~> HomObj v a b) -> a ~> (b ^ n)
  unpower :: (Ob (b :: k), Ob n) => a ~> (b ^ n) -> n ~> HomObj v a b

mapBase :: forall {k} {v} (n :: v) (a :: k) b. (Powered v k, Ob n) => a ~> b -> a ^ n ~> b ^ n
mapBase f =
  f //
    withObPower @v @k @a @n
      ( power @v @k @(a ^ n) @b @n
          (let g = unpower @v @k @a @n id in g // comp @v @(a ^ n) @a @b . leftUnitorInvWith (underlying @v f) . g)
      )

mapPower :: forall {k} {v} (a :: k) (n :: v) m. (Powered v k, Ob a) => (n ~> m) -> a ^ m ~> a ^ n
mapPower f = withObPower @v @k @a @m (power @v @k @(a ^ m) @a @n (unpower @v @k @a id . f)) \\ f

instance Powered Type Type where
  type a ^ n = n ~~> a
  withObPower r = r
  power f a n = f n a
  unpower f n a = f a n

instance (Enriched v (), Closed v, HomObj v '() '() ~ TerminalObject, Cartesian v) => Powered v () where
  type a ^ n = '()
  withObPower r = r
  power _ = U.Unit
  unpower U.Unit = terminate

class (HomObj v '(a1, a2) '(b1, b2) ~ (HomObj v a1 b1 && HomObj v a2 b2)) => HomObjIsProduct v a1 a2 b1 b2
instance (HomObj v '(a1, a2) '(b1, b2) ~ (HomObj v a1 b1 && HomObj v a2 b2)) => HomObjIsProduct v a1 a2 b1 b2
instance
  ( Powered v j
  , Powered v k
  , Enriched v (j, k)
  , forall (a :: (j, k)) (b :: (j, k)) a1 a2 b1 b2
     . (Ob a, a ~ '(a1, a2), Ob b, b ~ '(b1, b2)) => HomObjIsProduct v a1 a2 b1 b2
  , Cartesian v
  )
  => Powered v (j, k)
  where
  type '(a1, a2) ^ n = '(a1 ^ n, a2 ^ n)
  withObPower @'(a, b) @n r = withObPower @v @j @a @n (withObPower @v @k @b @n r)
  power @'(a1, a2) @'(b1, b2) f =
    withProObj @v @(~>) @a1 @b1 $
      withProObj @v @(~>) @a2 @b2 $
        power @v @j @a1 @b1 (fst @_ @(HomObj v a1 b1) @(HomObj v a2 b2) . f)
          :**: power @v @k @a2 @b2 (snd @_ @(HomObj v a1 b1) @(HomObj v a2 b2) . f)
  unpower @'(b1, b2) @n (f :**: g) = unpower @v @j @b1 @n f &&& unpower @v @k @b2 @n g \\ f \\ g

data (p :^: n) a b where
  Power :: (Ob a, Ob b) => {unPower :: n -> p a b} -> (p :^: n) a b
instance (Profunctor p) => Profunctor (p :^: n) where
  dimap l r (Power f) = l // r // Power \n -> dimap l r (f n)
  r \\ Power{} = r
instance (CategoryOf j, CategoryOf k) => Powered Type (j +-> k) where
  type a ^ n = a :^: n
  withObPower r = r
  power f = Prof \p -> p // Power \n -> unProf (f n) p
  unpower (Prof f) n = Prof \p -> unPower (f p) n