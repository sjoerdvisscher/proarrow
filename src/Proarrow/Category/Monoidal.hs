{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)

import Proarrow.Core (PRO, Promonad(..), CategoryOf(..), Profunctor (..), (:~>), lmap, rmap)
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Object (obj, Obj)
import Proarrow.Category.Instance.List (type (++), List (..), append)
import Proarrow.Profunctor.Composition ((:.:) (..), dimapComp)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Identity (Id (..))


type TENSOR k = PRO k (k, k)
type Tensor :: forall {k}. TENSOR k -> Constraint
class (Representable t, Ob @k (U t)) => Tensor (t :: PRO k (k, k)) where
  type U t :: k
  leftUnitor :: Obj a -> t % '(U t, a) ~> a
  leftUnitorInv :: Obj a -> a ~> t % '(U t, a)
  rightUnitor :: Obj a -> t % '(a, U t) ~> a
  rightUnitorInv :: Obj a -> a ~> t % '(a, U t)
  associator :: Obj a -> Obj b -> Obj c -> t % '(t % '(a, b), c) ~> t % '(a, t % '(b, c))
  associatorInv :: Obj a -> Obj b -> Obj c -> t % '(a, t % '(b, c)) ~> t % '(t % '(a, b), c)


type MONOIDAL k = PRO [k] [k]

class Promonad t => Monoidal (t :: MONOIDAL k) where
  par :: t as bs -> t cs ds -> t (as ++ cs) (bs ++ ds)



type family Fold (t :: PRO k (k, k)) (as :: [k]) :: k where
  Fold t '[] = U t
  Fold t '[a] = a
  Fold t (a ': as) = t % '(a, Fold t as)

fold :: forall {k} t as bs. Tensor (t :: PRO k (k, k)) => List (as :: [k]) bs -> Fold t as ~> Fold t bs
fold Nil = id
fold (Cons f Nil) = f
fold (Cons f fs@Cons{}) = repMap @t (f :**: fold @t fs)

concatFold
  :: forall {k} (t :: PRO k (k, k)) (as :: [k]) (bs :: [k]). (Ob as, Ob bs, Tensor t)
  => t % '(Fold t as, Fold t bs) ~> Fold t (as ++ bs)
concatFold =
  let fbs = fold @t (obj @bs)
      h :: forall cs. Obj cs -> t % '(Fold t cs, Fold t bs) ~> Fold t (cs ++ bs)
      h Nil = leftUnitor @t fbs
      h (Cons c Nil) = case obj @bs of
        Nil -> rightUnitor @t c
        Cons{} -> repMap @t (c :**: fbs)
      h (Cons c cs@Cons{}) =
        repMap @t (c :**: h cs) . associator @t c (fold @t cs) fbs
  in h (obj @as)

splitFold
  :: forall {k} (t :: PRO k (k, k)) (as :: [k]) (bs :: [k]). (Ob as, Ob bs, Tensor t)
  => Fold t (as ++ bs) ~> t % '(Fold t as, Fold t bs)
splitFold =
  let fbs = fold @t (obj @bs)
      h :: forall cs. Obj cs -> Fold t (cs ++ bs) ~> t % '(Fold t cs, Fold t bs)
      h Nil = leftUnitorInv @t fbs
      h (Cons c Nil) = case obj @bs of
        Nil -> rightUnitorInv @t c
        Cons{} -> repMap @t (c :**: fbs)
      h (Cons c cs@Cons{}) = associatorInv @t c (fold @t cs) fbs . repMap @t (c :**: h cs)
  in h (obj @as)



type Strictified :: PRO k (k, k) -> MONOIDAL k
data Strictified t as bs where
  Strictified :: (Ob as, Ob bs) => Fold t as ~> Fold t bs -> Strictified t as bs

instance Tensor (t :: PRO k (k, k)) => Profunctor (Strictified t :: MONOIDAL k) where
  dimap ls rs (Strictified f) = Strictified (fold @t rs . f . fold @t ls) \\ ls \\ rs
  r \\ Strictified f = r \\ f

instance Tensor (t :: PRO k (k, k)) => Promonad (Strictified t :: MONOIDAL k) where
  id :: forall (as :: [k]). Ob as => Strictified t as as
  id = Strictified (fold @t (obj @as))
  Strictified f . Strictified g = Strictified (f . g)

instance Tensor (t :: PRO k (k, k)) => Monoidal (Strictified t :: MONOIDAL k) where
  par (Strictified @as @bs f) (Strictified @cs @ds g) =
    Strictified (concatFold @t @bs @ds . repMap @t (f :**: g) . splitFold @t @as @cs)
      \\ (obj @as `append` obj @cs) \\ (obj @bs `append` obj @ds)


type Compose :: TENSOR (PRO k k)
data Compose p qr where
  Compose :: (Profunctor p, Profunctor q, Profunctor r) => p :~> q :.: r -> Compose p '(q, r)

instance CategoryOf k => Profunctor (Compose :: TENSOR (PRO k k)) where
  dimap (Prof l) (Prof r1 :**: Prof r2) (Compose f) = Compose (\(f . l -> p :.: q) -> r1 p :.: r2 q)
  r \\ Compose f = r \\ f

instance CategoryOf k => Representable (Compose :: TENSOR (PRO k k)) where
  type Compose % '(p, q) = p :.: q
  index (Compose f) = Prof f
  tabulate (Prof f) = Compose f
  repMap (f :**: g) = dimapComp f g

instance CategoryOf k => Tensor (Compose :: TENSOR (PRO k k)) where
  type U Compose = Id
  leftUnitor Prof{} = Prof \(Id f :.: p) -> lmap f p
  leftUnitorInv Prof{} = Prof \p -> Id id :.: p \\ p
  rightUnitor Prof{} = Prof \(p :.: Id f) -> rmap f p
  rightUnitorInv Prof{} = Prof \p -> p :.: Id id \\ p
  associator Prof{} Prof{} Prof{} = Prof \((p :.: q) :.: r) -> p :.: (q :.: r)
  associatorInv Prof{} Prof{} Prof{} = Prof \(p :.: (q :.: r)) -> (p :.: q) :.: r
