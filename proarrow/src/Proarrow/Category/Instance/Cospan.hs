{-# LANGUAGE PatternSynonyms #-}

-- | The category of __cospans__ in @k@: objects are those of @k@ (wrapped in 'CS'), and a morphism
-- @a '~>' b@ is a cospan @a -> x <- b@, composed by pushout. With the coproduct of @k@ as tensor
-- every object is a Frobenius monoid, giving a 'Proarrow.Category.Monoidal.Hypergraph.Hypergraph',
-- compact closed, dagger category. This is the archetypal setting for undirected wiring diagrams.
--
-- These are the decorated cospans of "Proarrow.Category.Instance.DecoratedCospan" without a
-- decoration, which is where their structure comes from.
module Proarrow.Category.Instance.Cospan
  ( COSPAN
  , CS
  , Cospan
  , pattern Cospan
  , Undecorated (..)
  , arr
  , coarr
  , Pushout
  , Pullback
  ) where

import Data.Kind (Type)
import Prelude (type (~))

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.Span (SPAN (..), Span (..))
import Proarrow.Category.Monoidal.Applicative (Alternative (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), tgt, type (+->))
import Proarrow.Functor (Functor (..), FunctorForRep (..))
import Proarrow.Limit.Pullback (HasPullbacks (..))

-- | The decoration that says nothing.
type Undecorated :: k -> Type
data Undecorated c = Undecorated

instance (CategoryOf k) => Functor (Undecorated :: k -> Type) where
  map _ Undecorated = Undecorated

instance (HasBinaryCoproducts k) => Alternative (Undecorated :: k -> Type) where
  empty () = Undecorated
  alt _ _ = Undecorated

type COSPAN :: Type -> Type
type COSPAN k = DECCOSPAN (Undecorated :: k -> Type)

-- | An object of @k@ as one of 'COSPAN' @k@.
type CS :: forall k. k -> COSPAN k
type CS @k = DC @k @Undecorated

type Cospan :: forall k. CAT (COSPAN k)
type Cospan @k = DecCospan @(Undecorated :: k -> Type)

-- | A cospan @a -> c <- b@.
pattern Cospan
  :: forall {k} {a :: COSPAN k} {b}. () => forall c a' b'. (a ~ CS a', b ~ CS b') => a' ~> c -> b' ~> c -> Cospan a b
pattern Cospan f g = DecCospan f g Undecorated

{-# COMPLETE Cospan #-}

arr :: (CategoryOf k) => (a :: k) ~> b -> Cospan (CS a) (CS b)
arr f = Cospan f (tgt f)

coarr :: (CategoryOf k) => (a :: k) ~> b -> Cospan (CS b) (CS a)
coarr f = Cospan (tgt f) f

data family Pushout :: SPAN k +-> COSPAN k
instance (HasPushouts k, HasCoproducts k, HasPullbacks k) => FunctorForRep (Pushout :: SPAN k +-> COSPAN k) where
  type Pushout @ (SP a) = CS a
  fmap (Span l r) = pushout l r Cospan

data family Pullback :: COSPAN k +-> SPAN k
instance (HasPushouts k, HasCoproducts k, HasPullbacks k) => FunctorForRep (Pullback :: COSPAN k +-> SPAN k) where
  type Pullback @ (CS a) = SP a
  fmap (Cospan l r) = pullback l r Span
