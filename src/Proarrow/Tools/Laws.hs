{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Tools.Laws where

import Data.Data ((:~:) (..))
import Data.Kind (Constraint, Type)
import GHC.TypeLits (KnownSymbol, Symbol)
import Prelude (Show)

import Proarrow.Category.Instance.Free (FREE (..), Free, Show2, emb)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), dimapDefault)

data family Var (cs :: [Kind -> Constraint]) (a :: Symbol) (b :: Symbol)
class Laws (cs :: [Kind -> Constraint]) where
  type EqTypes cs :: [FREE cs (Var cs)]
  laws :: [AssertEq cs]

data instance Var '[] a b where
  F :: Var '[] "A" "B"
  G :: Var '[] "B" "C"
  H :: Var '[] "C" "D"
deriving instance Show (Var '[] a b)
instance Laws '[] where
  type EqTypes '[] = '[EMB "A", EMB "B", EMB "C", EMB "D"]
  laws =
    let f = emb F; g = emb G; h = emb H
    in [ id . f :=: f
       , f . id :=: f
       , (h . g) . f :=: h . (g . f)
       ]

infix 0 :=:
type AssertEq :: [Kind -> Constraint] -> Type
data AssertEq cs where
  (:=:)
    :: forall {cs} (a :: FREE cs (Var cs)) (b :: FREE cs (Var cs))
     . (a `Elem` EqTypes cs, b `Elem` EqTypes cs) => Free a b -> Free a b -> AssertEq cs
deriving instance (Show2 (Var cs)) => Show (AssertEq cs)

data Place as a where
  Here :: Place (a ': as) a
  There :: (b `Elem` as) => Place (a ': as) b

type Elem :: forall {a}. a -> [a] -> Constraint
class c `Elem` cs where
  place :: Place cs c
instance {-# OVERLAPPABLE #-} (c `Elem` cs) => c `Elem` (d ': cs) where
  place = There
instance c `Elem` (c ': cs) where
  place = Here

data Sym a b where
  Sym :: (KnownSymbol a, KnownSymbol b) => a :~: b -> Sym a b
instance Profunctor (Sym :: CAT Symbol) where
  dimap = dimapDefault
  r \\ Sym{} = r
instance Promonad (Sym :: CAT Symbol) where
  id = Sym Refl
  Sym Refl . Sym Refl = Sym Refl
instance CategoryOf Symbol where
  type (~>) = Sym
  type Ob a = (KnownSymbol a)
