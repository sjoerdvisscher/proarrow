{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Instance.Star where

import Data.Functor.Compose (Compose (..))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Category.Instance.Nat (ApplyAction, Nat' (..), type (.->) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (ProdAction, SubAction)
import Proarrow.Category.Monoidal.Applicative (Alternative (..), Applicative (..))
import Proarrow.Category.Monoidal.Distributive (Distributive, Traversable (..), baseTraverse)
import Proarrow.Category.Monoidal.Strength (MonStrong, Strong (..))
import Proarrow.Colimit.BinaryCoproduct (COPROD (..), Coprod (..), HasBinaryCoproducts (..), HasCoproducts, (++))
import Proarrow.Colimit.Initial (initiate)
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), lmap, obj, (:~>), type (+->))
import Proarrow.Functor (Functor (..), Prelude (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

type Star' :: j .-> k -> j +-> k
data Star' f a b where
  Star' :: (Ob b) => {unStar :: a ~> f b} -> Star' (NT f) a b

type Star f = Star' (NT f)
pattern Star :: () => (Ob b) => (a ~> f b) -> Star f a b
pattern Star f = Star' f
{-# COMPLETE Star #-}

instance (Functor f) => Profunctor (Star f) where
  dimap = dimapRep
  r \\ Star f = r \\ f

instance (CategoryOf j, CategoryOf k) => Functor (Star' :: (j .-> k) -> j +-> k) where
  map (Nat' n) = Prof \(Star f) -> Star (n . f)

instance (Functor f) => Representable (Star f) where
  type Star f % a = f a
  index = unStar
  tabulate = Star
  repMap = map

instance (Profunctor p) => Promonad (Star ((:+:) p)) where
  id = Star (Prof InjR)
  Star (Prof l) . Star (Prof r) = Star (Prof (\a -> case r a of InjL p -> InjL p; InjR b -> l b))

instance (P.Monad m) => Promonad (Star (Prelude m)) where
  id = Star (Prelude . P.pure)
  Star g . Star f = Star \a -> Prelude (unPrelude (f a) P.>>= (unPrelude . g))

composeStar :: (Functor f) => Star f :.: Star g :~> Star (Compose f g)
composeStar (Star f :.: Star g) = Star (Compose . map g . f)

instance (Applicative f, Monoidal j, Monoidal k) => MonoidalProfunctor (Star (f :: j -> k)) where
  one = Star (pure id)
  Star @a f ** Star @b g = withOb2 @_ @a @b (Star (liftA2 @f @a @b id . (f ** g)))

instance (Functor f, HasCoproducts j, HasCoproducts k) => MonoidalProfunctor (Coprod (Star (f :: j -> k))) where
  one = Coprod (Star initiate)
  Coprod (Star @a f) ** Coprod (Star @b g) = withObCoprod @_ @a @b (Coprod (Star (map (lft @_ @a @b) . f ||| map (rgt @_ @a @b) . g)))

-- Hmm, another wrapper required...
type CoprodDom :: j +-> k -> COPROD j +-> k
data CoprodDom p a b where
  Co :: {unCo :: p a b} -> CoprodDom p a (COPR b)
instance (Profunctor p) => Profunctor (CoprodDom p) where
  dimap l (Coprod (Id r)) (Co p) = Co (dimap l r p)
  r \\ Co p = r \\ p

instance (Alternative f, Monoidal k, Distributive j) => MonoidalProfunctor (CoprodDom (Star (f :: j -> k))) where
  one = Co (Star empty)
  Co (Star @a f) ** Co (Star @b g) = let ab = obj @a +++ obj @b in Co (Star (alt @f @a @b ab . (f ** g))) \\ ab

instance (P.Functor f) => Strong ProdAction (Star (Prelude f)) where
  act (Star k) = Star (\(a, x) -> P.fmap (a,) (k x))

instance (P.Applicative f) => Strong (SubAction P.Traversable ApplyAction) (Star (Prelude f)) where
  act (Star f) = Star (P.traverse f)

instance Traversable (Star P.Maybe) where
  traverse (Star a2mb :.: p) = lmap a2mb go :.: Star id
    where
      go =
        dimap
          (P.maybe (P.Left ()) P.Right)
          (P.const P.Nothing ||| P.Just)
          (one ++ p)

instance Traversable (Star []) where
  traverse (Star a2bs :.: p) = lmap a2bs go :.: Star id
    where
      go =
        dimap
          (\case [] -> P.Left (); (x : xs) -> P.Right (x, xs))
          (P.const [] ||| P.uncurry (:))
          (one ++ (p ** go))

starTraverse
  :: forall {k} t f a b
   . (Applicative (f :: k -> k), Functor t, Traversable (Star t), MonStrong (Star f), HasCoproducts k, Ob b)
  => (a ~> f b) -> t a ~> f (t b)
starTraverse = baseTraverse @(Star t) @(Star f)

instance (Functor f, Thin k) => ThinProfunctor (Star f :: j +-> k) where
  type HasArrow (Star f :: j +-> k) a b = HasArrow (Hom k) a (f b)
  arr = Star arr
  withArr (Star f) r = withArr f r