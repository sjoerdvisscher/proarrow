module Proarrow.Category.Instance.Ap where

import Control.Applicative (Applicative (..), liftA3)
import Data.Kind (Type)
import Prelude (($))

import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))

type data AP (f :: Type -> Type) k = A k
type instance UN A (A k) = k

type Ap :: (j +-> k) -> AP f j +-> AP f k
data Ap p a b where
  Ap :: forall {j} {k} a b f p. (Ob a, Ob b) => {unAp :: f (p a b)} -> Ap p (A a :: AP f j) (A b :: AP f k)

instance (Applicative f, Profunctor p) => Profunctor (Ap (p :: j +-> k) :: AP f j +-> AP f k) where
  dimap (Ap l) (Ap r) (Ap x) = Ap (liftA3 dimap l r x)
  r \\ Ap{} = r
instance (Applicative f, Promonad p) => Promonad (Ap (p :: k +-> k) :: AP f k +-> AP f k) where
  id = Ap (pure id)
  Ap f . Ap g = Ap (liftA2 (.) f g)
instance (Applicative f, CategoryOf k) => CategoryOf (AP f k) where
  type (~>) = Ap (~>)
  type Ob a = (Is A a, Ob (UN A a))

instance (Applicative f, HasInitialObject k) => HasInitialObject (AP f k) where
  type InitialObject = A InitialObject
  initiate = Ap (pure initiate)
instance (Applicative f, HasTerminalObject k) => HasTerminalObject (AP f k) where
  type TerminalObject = A TerminalObject
  terminate = Ap (pure terminate)
instance (Applicative f, HasBinaryProducts k) => HasBinaryProducts (AP f k) where
  type a && b = A (UN A a && UN A b)
  withObProd @(A a) @(A b) r = withObProd @k @a @b r
  fst @(A a) @(A b) = withObProd @k @a @b $ Ap (pure (fst @_ @a @b))
  snd @(A a) @(A b) = withObProd @k @a @b $ Ap (pure (snd @_ @a @b))
  Ap @al @bl f &&& Ap @ar @br g = withObProd @k @al @ar $ withObProd @k @bl @br $ Ap (liftA2 (&&&) f g)
instance (Applicative f, HasBinaryCoproducts k) => HasBinaryCoproducts (AP f k) where
  type a || b = A (UN A a || UN A b)
  withObCoprod @(A a) @(A b) r = withObCoprod @k @a @b r
  lft @(A a) @(A b) = withObCoprod @k @a @b $ Ap (pure (lft @_ @a @b))
  rgt @(A a) @(A b) = withObCoprod @k @a @b $ Ap (pure (rgt @_ @a @b))
  Ap @al @bl f ||| Ap @ar @br g = withObCoprod @k @al @ar $ withObCoprod @k @bl @br $ Ap (liftA2 (|||) f g)

instance (Applicative f, MonoidalProfunctor p) => MonoidalProfunctor (Ap (p :: j +-> k) :: AP f j +-> AP f k) where
  par0 = Ap (pure par0)
  Ap @al @bl l `par` Ap @ar @br r = withOb2 @k @al @ar $ withOb2 @j @bl @br $ Ap (liftA2 par l r)

instance (Applicative f, Monoidal k) => Monoidal (AP f k) where
  type Unit = A Unit
  type a ** b = A (UN A a ** UN A b)
  withOb2 @(A a) @(A b) r = withOb2 @_ @a @b r
  leftUnitor @(A a) = withOb2 @_ @Unit @a $ Ap (pure leftUnitor)
  leftUnitorInv @(A a) = withOb2 @_ @Unit @a $ Ap (pure leftUnitorInv)
  rightUnitor @(A a) = withOb2 @_ @a @Unit $ Ap (pure rightUnitor)
  rightUnitorInv @(A a) = withOb2 @_ @a @Unit $ Ap (pure rightUnitorInv)
  associator @(A a) @(A b) @(A c) = withOb2 @_ @a @b $ withOb2 @_ @b @c $ withOb2 @_ @a @(b ** c) $ withOb2 @_ @(a ** b) @c $
    Ap (pure (associator @_ @a @b @c))
  associatorInv @(A a) @(A b) @(A c) = withOb2 @_ @a @b $ withOb2 @_ @b @c $ withOb2 @_ @a @(b ** c) $ withOb2 @_ @(a ** b) @c $
    Ap (pure (associatorInv @_ @a @b @c))

instance (Applicative f, SymMonoidal k) => SymMonoidal (AP f k) where
  swap @(A a) @(A b) = withOb2 @_ @a @b $ withOb2 @_ @b @a $ Ap (pure (swap @_ @a @b))