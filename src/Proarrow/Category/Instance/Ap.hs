module Proarrow.Category.Instance.Ap where

import Control.Applicative (Applicative (..), liftA3)
import Data.Kind (Type)
import Prelude (($))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Applicative qualified as A
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))

type data AP (f :: Type -> Type) k = A k
type instance UN A (A k) = k

type Ap :: (j +-> k) -> AP f j +-> AP f k
data Ap p a b where
  Ap :: forall {j} {k} a b f p. (Ob a, Ob b) => {unAp :: f (p a b)} -> Ap p (A a :: AP f j) (A b :: AP f k)

arr :: (Applicative f, Profunctor p) => p a b -> Ap p (A a) (A b :: AP f k)
arr f = Ap (pure f) \\ f

instance (Applicative f, Profunctor p) => Profunctor (Ap (p :: j +-> k) :: AP f j +-> AP f k) where
  dimap (Ap l) (Ap r) (Ap x) = Ap (liftA3 dimap l r x)
  r \\ Ap{} = r
instance (Applicative f, Promonad p) => Promonad (Ap (p :: k +-> k) :: AP f k +-> AP f k) where
  id = Ap (pure id)
  Ap f . Ap g = Ap (liftA2 (.) f g)
instance (Applicative f, CategoryOf k) => CategoryOf (AP f k) where
  type (~>) = Ap (~>)
  type Ob a = (Is A a, Ob (UN A a))

instance (Applicative f, CategoryOf k) => Functor (A :: k -> AP f k) where
  map = arr
instance (Applicative f, Monoidal k) => A.Applicative (A :: k -> AP f k) where
  pure = arr
  liftA2 = arr

instance (Applicative f, HasInitialObject k) => HasInitialObject (AP f k) where
  type InitialObject = A InitialObject
  initiate = arr initiate
instance (Applicative f, HasTerminalObject k) => HasTerminalObject (AP f k) where
  type TerminalObject = A TerminalObject
  terminate = arr terminate
instance (Applicative f, HasBinaryProducts k) => HasBinaryProducts (AP f k) where
  type a && b = A (UN A a && UN A b)
  withObProd @(A a) @(A b) r = withObProd @k @a @b r
  fst @(A a) @(A b) = arr (fst @_ @a @b)
  snd @(A a) @(A b) = arr (snd @_ @a @b)
  Ap @_ @bl f &&& Ap @_ @br g = withObProd @k @bl @br $ Ap (liftA2 (&&&) f g)
  Ap @al @bl f *** Ap @ar @br g = withObProd @k @al @ar $ withObProd @k @bl @br $ Ap (liftA2 (***) f g)
instance (Applicative f, HasBinaryCoproducts k) => HasBinaryCoproducts (AP f k) where
  type a || b = A (UN A a || UN A b)
  withObCoprod @(A a) @(A b) r = withObCoprod @k @a @b r
  lft @(A a) @(A b) = map (lft @_ @a @b)
  rgt @(A a) @(A b) = map (rgt @_ @a @b)
  Ap @al f ||| Ap @ar g = withObCoprod @k @al @ar $ Ap (liftA2 (|||) f g)
  Ap @al @bl f +++ Ap @ar @br g = withObCoprod @k @al @ar $ withObCoprod @k @bl @br $ Ap (liftA2 (+++) f g)

instance (Applicative f, MonoidalProfunctor p) => MonoidalProfunctor (Ap (p :: j +-> k) :: AP f j +-> AP f k) where
  par0 = arr par0
  Ap @al @bl l `par` Ap @ar @br r = withOb2 @k @al @ar $ withOb2 @j @bl @br $ Ap (liftA2 par l r)

instance (Applicative f, Monoidal k) => Monoidal (AP f k) where
  type Unit = A Unit
  type a ** b = A (UN A a ** UN A b)
  withOb2 @(A a) @(A b) r = withOb2 @_ @a @b r
  leftUnitor = arr leftUnitor
  leftUnitorInv = arr leftUnitorInv
  rightUnitor = arr rightUnitor
  rightUnitorInv = arr rightUnitorInv
  associator @(A a) @(A b) @(A c) = arr (associator @_ @a @b @c)
  associatorInv @(A a) @(A b) @(A c) = arr (associatorInv @_ @a @b @c)

instance (Applicative f, SymMonoidal k) => SymMonoidal (AP f k) where
  swap @(A a) @(A b) = arr (swap @_ @a @b)