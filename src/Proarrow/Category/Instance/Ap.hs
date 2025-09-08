module Proarrow.Category.Instance.Ap where

import Control.Applicative (liftA3)
import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))

type data AP (f :: Type -> Type) k = A k
type instance UN A (A k) = k

type Ap :: (j +-> k) -> AP f j +-> AP f k
data Ap p a b where
  Ap :: forall {j} {k} a b f p. (Ob a, Ob b) => {unAp :: f (p a b)} -> Ap p (A a :: AP f j) (A b :: AP f k)

instance (P.Applicative f, Profunctor p) => Profunctor (Ap (p :: j +-> k) :: AP f j +-> AP f k) where
  dimap (Ap l) (Ap r) (Ap x) = Ap (liftA3 dimap l r x)
  r \\ Ap{} = r
instance (P.Applicative f, Promonad p) => Promonad (Ap (p :: k +-> k) :: AP f k +-> AP f k) where
  id = Ap (P.pure id)
  Ap f . Ap g = Ap (P.liftA2 (.) f g)
instance (P.Applicative f, CategoryOf k) => CategoryOf (AP f k) where
  type (~>) = Ap (~>)
  type Ob a = (Is A a, Ob (UN A a))

instance (P.Applicative f, HasInitialObject k) => HasInitialObject (AP f k) where
  type InitialObject = A InitialObject
  initiate = Ap (P.pure initiate)
instance (P.Applicative f, HasTerminalObject k) => HasTerminalObject (AP f k) where
  type TerminalObject = A TerminalObject
  terminate = Ap (P.pure terminate)
instance (P.Applicative f, HasBinaryProducts k) => HasBinaryProducts (AP f k) where
  type a && b = A (UN A a && UN A b)
  withObProd @(A a) @(A b) r = withObProd @k @a @b r
  fst @(A a) @(A b) = withObProd @k @a @b P.$ Ap (P.pure (fst @_ @a @b))
  snd @(A a) @(A b) = withObProd @k @a @b P.$ Ap (P.pure (snd @_ @a @b))
  Ap @al @bl f &&& Ap @ar @br g = withObProd @k @al @ar P.$ withObProd @k @bl @br P.$ Ap (P.liftA2 (&&&) f g)
instance (P.Applicative f, HasBinaryCoproducts k) => HasBinaryCoproducts (AP f k) where
  type a || b = A (UN A a || UN A b)
  withObCoprod @(A a) @(A b) r = withObCoprod @k @a @b r
  lft @(A a) @(A b) = withObCoprod @k @a @b P.$ Ap (P.pure (lft @_ @a @b))
  rgt @(A a) @(A b) = withObCoprod @k @a @b P.$ Ap (P.pure (rgt @_ @a @b))
  Ap @al @bl f ||| Ap @ar @br g = withObCoprod @k @al @ar P.$ withObCoprod @k @bl @br P.$ Ap (P.liftA2 (|||) f g)