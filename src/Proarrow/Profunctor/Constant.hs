module Proarrow.Profunctor.Constant where

import Data.Kind (Type, Constraint)
import Data.Monoid qualified as P
import Prelude qualified as P

import Proarrow.Category.Monoidal.Action (Costrong (..), MonoidalAction (..), SelfAction, Strong (..), fromSelfAct)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, rmap, (//), type (+->), Optic)
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object.BinaryCoproduct (COPROD)
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..))
import Proarrow.Profunctor.Corepresentable (Corep, corep)
import Proarrow.Profunctor.Representable (Rep (..), rep)

data family Constant :: k -> j +-> k
instance (CategoryOf j, CategoryOf k, Ob c) => FunctorForRep (Constant c :: j +-> k) where
  type Constant c @ a = c
  fmap _ = id

instance (Cartesian k, SelfAction k, Ob c) => Strong k (Rep (Constant c) :: k +-> k) where
  act @m @m' @x @y g (Rep f) = withObAct @k @k @m' @y (Rep (f . snd @k @m @x . fromSelfAct @m @x)) \\ g \\ f

instance Strong (COPROD Type) (Rep (Constant (P.First c)) :: Type +-> Type) where
  act _ (Rep f) = Rep (P.either (P.const (P.First P.Nothing)) f)

type Getting r s a = Rep (Constant r) a a -> Rep (Constant r) s s

view :: forall {k} (s :: k) a. (CategoryOf k, Ob a) => Getting a s a -> s ~> a
view l = rep @(Constant a) l id

infixl 8 ^.
(^.) :: s -> Getting a s a -> a
(^.) s l = view l s

type AReview r s a = Corep (Constant r) a a -> Corep (Constant r) s s

review :: forall {k} (t :: k) b. (CategoryOf k, Ob b) => AReview b t b -> b ~> t
review l = corep @(Constant b) l id

infixr 8 #
(#) :: forall {k} (t :: k) b. (CategoryOf k, Ob b) => AReview b t b -> b ~> t
(#) = review

data Re p s t a b where
  Re :: (Ob a, Ob b) => {unRe :: p b a -> p t s} -> Re p s t a b

class (forall p a b. coc p => c (Re p a b)) => InvertableOptic (c :: j +-> k -> Constraint) (coc :: k +-> j -> Constraint) | c -> coc
instance InvertableOptic (Strong m) (Costrong m)
instance InvertableOptic (Costrong m) (Strong m)
instance InvertableOptic Profunctor Profunctor

class (l p, r p) => (l :&&: r) p
instance (l p, r p) => (l :&&: r) p
instance (InvertableOptic l l', InvertableOptic r r') => InvertableOptic (l :&&: r) (l' :&&: r')

re :: (Ob a, Ob b, InvertableOptic c coc) => Optic c s t a b -> Optic coc b a t s
re l = unRe (l (Re id))

instance (Profunctor p) => Profunctor (Re p s t) where
  dimap l r (Re f) = Re (f . dimap r l) \\ l \\ r
  r \\ Re{} = r
instance (Strong m p) => Costrong m (Re p s t) where
  coact @a (Re f) = Re \pyx -> f (act (obj @a) pyx)
instance (Costrong m p) => Strong m (Re p s t) where
  act @a @b @x @y g (Re f) = g //
    withObAct @m @_ @a @x P.$
      withObAct @m @_ @b @y P.$
        Re \payax -> f (coact @_ @_ @b (rmap (act g (obj @x)) payax))