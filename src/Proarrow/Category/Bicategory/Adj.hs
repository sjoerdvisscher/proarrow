module Proarrow.Category.Bicategory.Adj where

import Proarrow.Category.Bicategory
  ( Bicategory (..)
  , Comonad (..)
  , IsPath (..)
  , Monad (..)
  , Path (..)
  , SPath (..)
  , withUnital
  , type (+++)
  )
import Proarrow.Category.Instance.Simplex (Nat (..), Simplex (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Object (src, tgt)

type data AB = A | B

type ABK :: CAT AB
type data ABK a b where
  L :: ABK A B
  R :: ABK B A

type ADJK :: CAT AB
type data ADJK i j = AK (Path ABK i j)
type instance UN AK (AK ps) = ps

type Adj :: CAT (ADJK i j)
data Adj ps qs where
  AdjNil :: Adj (AK Nil) (AK Nil)
  AdjR :: Adj (AK ps) (AK qs) -> Adj (AK (R ::: ps)) (AK (R ::: qs))
  AdjL :: Adj (AK ps) (AK qs) -> Adj (AK (L ::: ps)) (AK (L ::: qs))
  AdjCup :: Adj (AK ps) qs -> Adj (AK (R ::: L ::: ps)) qs
  AdjCap :: Adj ps (AK qs) -> Adj ps (AK (L ::: R ::: qs))

class IsRL rl where rOrL :: Adj (AK ps) (AK qs) -> Adj (AK (rl ::: ps)) (AK (rl ::: qs))
instance IsRL L where rOrL = AdjL
instance IsRL R where rOrL = AdjR

instance Profunctor (Adj :: CAT (ADJK a b)) where
  dimap = dimapDefault
  r \\ AdjNil = r
  r \\ AdjR f = r \\ f
  r \\ AdjL f = r \\ f
  r \\ AdjCup f = r \\ f
  r \\ AdjCap f = r \\ f
instance Promonad (Adj :: CAT (ADJK a b)) where
  id :: forall (ps :: ADJK a b). (Ob ps) => Adj ps ps
  id = go (singPath @(UN AK ps))
    where
      go :: forall ps'. SPath ps' -> Adj (AK ps') (AK ps')
      go SNil = AdjNil
      go (SCons @rl p ps) = rOrL @rl (go ps) \\ p
  AdjNil . f = f
  f . AdjNil = f
  AdjR f . AdjR g = AdjR (f . g)
  AdjL f . AdjL g = AdjL (f . g)
  f . AdjCup g = AdjCup (f . g)
  AdjCap f . g = AdjCap (f . g)
  AdjL (AdjR f) . AdjCap g = AdjCap (f . g)
  AdjCup f . AdjR (AdjL g) = AdjCup (f . g)
  AdjL (AdjCup f) . AdjCap g = AdjL f . g -- zigzag
  AdjCup f . AdjR (AdjCap g) = f . AdjR g -- zagzig

instance CategoryOf (ADJK a b) where
  type (~>) = Adj
  type Ob ps = (Is AK ps)

-- | The walking adjunction
instance Bicategory ADJK where
  type Ob0 ADJK a = (IsRL a)
  type I = AK Nil
  type ps `O` qs = AK (UN AK ps +++ UN AK qs)
  r \\\ AdjNil = r
  r \\\ AdjR f = r \\\ f
  r \\\ AdjL f = r \\\ f
  r \\\ AdjCup f = r \\\ f
  r \\\ AdjCap f = r \\\ f
  o :: forall {a} {b} (ps :: ADJK a b) qs rs ss. (ps ~> qs) -> (rs ~> ss) -> (ps `O` rs) ~> (qs `O` ss)
  o = o
  -- AdjNil `o` f = f \\ f
  -- f `o` AdjNil = f -- withUnital @(UN AK ps) (withUnital @(UN AK qs) f) \\ f
  -- AdjR f `o` g = AdjR (f `o` g)
  -- AdjL f `o` g = AdjL (f `o` g)
  -- AdjCup f `o` g = AdjCup (f `o` g)
  -- AdjCap f `o` g = AdjCap (f `o` g)
  leftUnitor AdjNil = AdjNil
  leftUnitor (AdjR f) = AdjR f

type family RepLR (n :: Nat) :: Path ABK A A where
  RepLR Z = Nil
  RepLR (S n) = L ::: R ::: RepLR n

-- | Adj(A, A) is the walking monoid
fromSimplex :: Simplex a b -> Adj (AK (RepLR a)) (AK (RepLR b))
fromSimplex ZZ = AdjNil
fromSimplex (Y n) = AdjCap (fromSimplex n)
fromSimplex (X (Y n)) = AdjL (AdjR (fromSimplex n))
fromSimplex (X (X n)) = fromSimplex (X n) . AdjL (AdjCup (AdjR (src (fromSimplex n))))

type family CountLR (ps :: Path ABK A A) :: Nat where
  CountLR Nil = Z
  CountLR (L ::: ps) = S (CountLR' ps)

type family CountLR' (ps :: Path ABK B A) :: Nat where
  CountLR' (R ::: n) = CountLR n

toSimplex :: Adj (AK a) (AK b) -> Simplex (CountLR a) (CountLR b)
toSimplex AdjNil = ZZ
toSimplex (AdjCap f) = Y (toSimplex f)
toSimplex (AdjL f) = go f id
  where
    go :: Adj (AK f) (AK g) -> (Simplex (S (CountLR' f)) (S (CountLR' g)) -> r) -> r
    go (AdjR g) xny = xny (X (Y (toSimplex g)))
    go (AdjCup g) xny = go g (xny . X)

type family RepRL (n :: Nat) :: Path ABK B B where
  RepRL Z = Nil
  RepRL (S n) = R ::: L ::: RepRL n

-- | Adj(B, B) is the walking comonoid
fromSimplexOp :: Simplex b a -> Adj (AK (RepRL a)) (AK (RepRL b))
fromSimplexOp ZZ = AdjNil
fromSimplexOp (Y n) = AdjCup (fromSimplexOp n)
fromSimplexOp (X (Y n)) = AdjR (AdjL (fromSimplexOp n))
fromSimplexOp (X (X n)) = AdjR (AdjCap (AdjL (tgt (fromSimplexOp n)))) . fromSimplexOp (X n)

type family CountRL (ps :: Path ABK B B) :: Nat where
  CountRL Nil = Z
  CountRL (R ::: ps) = S (CountRL' ps)

type family CountRL' (ps :: Path ABK A B) :: Nat where
  CountRL' (L ::: n) = CountRL n

toSimplexOp :: Adj (AK a) (AK b) -> Simplex (CountRL b) (CountRL a)
toSimplexOp AdjNil = ZZ
toSimplexOp (AdjCup f) = Y (toSimplexOp f)
toSimplexOp (AdjR f) = go f id
  where
    go :: Adj (AK f) (AK g) -> (Simplex (S (CountRL' g)) (S (CountRL' f)) -> r) -> r
    go (AdjL g) xny = xny (X (Y (toSimplexOp g)))
    go (AdjCap g) xny = go g (xny . X)

instance Monad (AK (L ::: R ::: Nil)) where
  eta = AdjCap AdjNil
  mu = AdjL (AdjCup (AdjR AdjNil))

-- instance Comonad (R ::: L ::: Nil) where
--   epsilon = AdjCup AdjNil
--   delta = AdjR (AdjCap (AdjL AdjNil))

type ARRK :: CAT AB
type data ARRK a b where
  IDA :: ARRK A A
  A2B :: ARRK A B
  IDB :: ARRK B B

type Arr :: CAT (ARRK i j)
data Arr a b where
  ArrId :: (Ob a) => Arr a a

instance Profunctor (Arr :: CAT (ARRK i j)) where
  dimap = dimapDefault
  r \\ ArrId = r
instance Promonad (Arr :: CAT (ARRK i j)) where
  id = ArrId
  ArrId . ArrId = ArrId
instance CategoryOf (ARRK i j) where
  type (~>) = Arr
  type Ob a = ()

instance Bicategory ARRK where
  type Ob0 ARRK a = ()
  r \\\ ArrId = r
  ArrId `o` ArrId = _

type family Arr2Adj (ps :: Path ARRK a b) :: Path ADJK a b
type instance Arr2Adj (IDA ::: ps) = Arr2Adj ps
type instance Arr2Adj (IDB ::: ps) = Arr2Adj ps
type instance Arr2Adj (A2B ::: ps) = AK (L ::: Nil) ::: Arr2Adj ps

-- type AdjSq :: DOUBLE ADJK ARRK
-- data AdjSq ps qs fs gs where
--   AdjSq :: ps +++ Arr2Adj gs ~> Arr2Adj fs +++ qs -> AdjSq ps qs fs gs
-- instance Double ADJK ARRK where
--   type Sq ADJK ARRK = AdjSq
--   object = AdjSq id
--   hArr f = AdjSq f
--   AdjSq f ||| AdjSq g = AdjSq (f `o` g)
--   vArr ArrId = AdjSq id
--   AdjSq f === AdjSq g = AdjSq (f `o` g)
