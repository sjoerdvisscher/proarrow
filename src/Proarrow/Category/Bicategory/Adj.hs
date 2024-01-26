module Proarrow.Category.Bicategory.Adj where

import Proarrow.Core (CAT, Profunctor(..), Promonad(..), CategoryOf(..), dimapDefault)
import Proarrow.Category.Bicategory (Path(..), type (+++), BICAT, Bicategory (..), IsPath(..), SPath(..), withUnital)
import Proarrow.Category.Instance.Simplex (Nat(..), Simplex(..))
import Proarrow.Object (src, tgt)

type data AB = A | B

type data ADJK a b where
  L :: ADJK A B
  R :: ADJK B A

type Adj :: BICAT ADJK
data Adj ps qs where
  AdjNil :: Adj Nil Nil
  AdjR :: Adj ps qs -> Adj (R ::: ps) (R ::: qs)
  AdjL :: Adj ps qs -> Adj (L ::: ps) (L ::: qs)
  AdjCup :: Adj ps qs -> Adj (R ::: L ::: ps) qs
  AdjCap :: Adj ps qs -> Adj ps (L ::: R ::: qs)

class IsRL rl where rOrL :: Adj ps qs -> Adj (rl ::: ps) (rl ::: qs)
instance IsRL L where rOrL = AdjL
instance IsRL R where rOrL = AdjR

instance Profunctor (Adj :: CAT (Path ADJK a b)) where
  dimap = dimapDefault
  r \\ AdjNil = r
  r \\ AdjR f = r \\ f
  r \\ AdjL f = r \\ f
  r \\ AdjCup f = r \\ f
  r \\ AdjCap f = r \\ f
instance Promonad (Adj :: CAT (Path ADJK a b)) where
  id :: forall (ps :: Path ADJK a b). Ob ps => Adj ps ps
  id = go (singPath @ps) where
    go :: forall ps'. SPath ps' -> Adj ps' ps'
    go SNil = AdjNil
    go (SCons @rl ps) = rOrL @rl (go ps)
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

instance CategoryOf (Path ADJK a b) where
  type (~>) = Adj
  type Ob ps = IsPath ps

-- | The walking adjunction
instance Bicategory ADJK where
  type Ob0 ADJK a = ()
  type Ob1 ADJK p = IsRL p
  r \\\ AdjNil =r
  r \\\ AdjR f = r \\\ f
  r \\\ AdjL f = r \\\ f
  r \\\ AdjCup f = r \\\ f
  r \\\ AdjCap f = r \\\ f
  o :: forall {a} {b} (ps :: Path ADJK a b) qs rs ss. (ps ~> qs) -> (rs ~> ss) -> (ps +++ rs) ~> (qs +++ ss)
  AdjNil `o` f = f
  f `o` AdjNil = withUnital @ps (withUnital @qs f) \\ f
  AdjR f `o` g = AdjR (f `o` g)
  AdjL f `o` g = AdjL (f `o` g)
  AdjCup f `o` g = AdjCup (f `o` g)
  AdjCap f `o` g = AdjCap (f `o` g)

type family RepLR (n :: Nat) :: Path ADJK A A where
  RepLR Z = Nil
  RepLR (S n) = L ::: R ::: RepLR n

-- | Adj(A, A) is the walking monoid
fromSimplex :: Simplex a b -> Adj (RepLR a) (RepLR b)
fromSimplex Z = AdjNil
fromSimplex (Y n) = AdjCap (fromSimplex n)
fromSimplex (X (Y n)) = AdjL (AdjR (fromSimplex n))
fromSimplex (X (X n)) = fromSimplex (X n) . AdjL (AdjCup (AdjR (src (fromSimplex n))))

type family CountLR (ps :: Path ADJK A A) :: Nat where
  CountLR Nil = Z
  CountLR (L ::: ps) = S (CountLR' ps)

type family CountLR' (ps :: Path ADJK B A) :: Nat where
  CountLR' (R ::: n) = CountLR n

toSimplex :: Adj a b -> Simplex (CountLR a) (CountLR b)
toSimplex AdjNil = Z
toSimplex (AdjCap f) = Y (toSimplex f)
toSimplex (AdjL f) = go f id
  where
    go :: Adj f g -> (Simplex (S (CountLR' f)) (S (CountLR' g)) -> r) -> r
    go (AdjR g) xny = xny (X (Y (toSimplex g)))
    go (AdjCup g) xny = go g (xny . X)

type family RepRL (n :: Nat) :: Path ADJK B B where
  RepRL Z = Nil
  RepRL (S n) = R ::: L ::: RepRL n

-- | Adj(B, B) is the walking comonoid
fromSimplexOp :: Simplex b a -> Adj (RepRL a) (RepRL b)
fromSimplexOp Z = AdjNil
fromSimplexOp (Y n) = AdjCup (fromSimplexOp n)
fromSimplexOp (X (Y n)) = AdjR (AdjL (fromSimplexOp n))
fromSimplexOp (X (X n)) = AdjR (AdjCap (AdjL (tgt (fromSimplexOp n)))) . fromSimplexOp (X n)

type family CountRL (ps :: Path ADJK B B) :: Nat where
  CountRL Nil = Z
  CountRL (R ::: ps) = S (CountRL' ps)

type family CountRL' (ps :: Path ADJK A B) :: Nat where
  CountRL' (L ::: n) = CountRL n

toSimplexOp :: Adj a b -> Simplex (CountRL b) (CountRL a)
toSimplexOp AdjNil = Z
toSimplexOp (AdjCup f) = Y (toSimplexOp f)
toSimplexOp (AdjR f) = go f id
  where
    go :: Adj f g -> (Simplex (S (CountRL' g)) (S (CountRL' f)) -> r) -> r
    go (AdjL g) xny = xny (X (Y (toSimplexOp g)))
    go (AdjCap g) xny = go g (xny . X)