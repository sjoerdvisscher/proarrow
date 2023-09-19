{-# LANGUAGE UndecidableInstances #-}
module Proarrow.Category.Instance.Subcategory where

import Proarrow.Core (CAT, OB, Category(..), Profunctor(..), type (~>), dimapDefault)

newtype SUB (ob :: OB k) = SUB { unSUB :: k }
type family UNSUB (a :: SUB (ob :: OB k)) :: k where UNSUB ('SUB k) = k

type Sub :: CAT (SUB ob)
data Sub a b where
  Sub :: (ob a, ob b) => a ~> b -> Sub ('SUB a :: SUB ob) ('SUB b)

type instance (~>) = Sub

instance Profunctor ((~>) :: CAT k) => Profunctor (Sub :: CAT (SUB (ob :: OB k))) where
  dimap = dimapDefault
  r \\ Sub p = r \\ p

-- | The subcategory with objects with instances of the given constraint `ob`.
instance Category ((~>) :: CAT k) => Category (Sub :: CAT (SUB (ob :: OB k))) where
  type Ob (a :: SUB ob) = (a ~ 'SUB (UNSUB a), Ob (UNSUB a), ob (UNSUB a))
  id = Sub id
  Sub f . Sub g = Sub (f . g)