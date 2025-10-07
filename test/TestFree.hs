{-# LANGUAGE LinearTypes #-}
module TestFree where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Discrete (DISCRETE(..), Discrete (..))
import Proarrow.Category.Instance.Free (FREE(..), Free(..), fold)
import Proarrow.Core (CategoryOf(..), type (+->), Promonad (..))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts, type (*!), (&&&))
import Proarrow.Profunctor.Representable (Representable (..), Rep)

type data TestTy = IntTy' | StringTy'
type IntTy = D IntTy'
type StringTy = D StringTy'
data Test a b where
  Show :: Test IntTy StringTy
  Read :: Test StringTy IntTy
  Succ :: Test IntTy IntTy
  Dup :: Test StringTy StringTy

shw :: (i :: FREE cs Test) ~> EMB IntTy %1 -> i ~> EMB StringTy
shw = Emb Show

read :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB IntTy
read = Emb Read

succ :: (i :: FREE cs Test) ~> EMB IntTy %1 -> i ~> EMB IntTy
succ = Emb Succ

dup :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB StringTy
dup = Emb Dup

test :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB StringTy
test x = dup (shw (succ (read x)))

test2
  :: (HasBinaryProducts (FREE cs Test)) => (i :: FREE cs Test) ~> EMB StringTy -> i ~> (EMB StringTy *! EMB StringTy)
test2 x = x &&& test x

data family Interp :: DISCRETE TestTy +-> Type
instance FunctorForRep Interp where
  type Interp @ IntTy = P.Int
  type Interp @ StringTy = P.String
  fmap Refl = id

-- >>> testFold "123"
-- ("123","124124")
testFold :: P.String -> (P.String, P.String)
testFold = fold @'[HasBinaryProducts] @(Rep Interp) interp (test2 Id)
  where
    interp :: Test x y -> Rep Interp % x ~> Rep Interp % y
    interp Show = P.show
    interp Read = P.read
    interp Succ = P.succ
    interp Dup = (\s -> s P.++ s)
