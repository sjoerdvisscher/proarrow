{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Adj where

import Data.Kind (Constraint, Type)
import Prelude (type (~))

import Proarrow.Category.Bicategory
  ( Adjunction_ (..)
  , Bicategory (..)
  , Comonad (..)
  , Monad (..)
  )
import Proarrow.Category.Bicategory qualified as Bi
import Proarrow.Category.Bicategory.Strictified (Assoc, Path (..), type (+++))
import Proarrow.Category.Equipment (Cotight, CotightAdjoint, Equipment (..), IsOb, Tight, TightAdjoint, WithObO2 (..))
import Proarrow.Category.Instance.Simplex (Nat (..), Simplex (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj)
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

type SAdj :: Path ABK i j -> Type
data SAdj p where
  SNil :: SAdj Nil
  SL :: (IsLRPath ps) => SAdj (L ::: ps)
  SR :: (IsLRPath ps) => SAdj (R ::: ps)

type IsLRPath :: forall {i} {j}. Path ABK i j -> Constraint
class (ps +++ Nil ~ ps, forall i h (qs :: Path ABK k h) (rs :: Path ABK h i). Assoc ps qs rs) => IsLRPath (ps :: Path ABK j k) where
  singPath :: SAdj ps
  withIsPath2 :: (IsLRPath qs) => ((IsLRPath (ps +++ qs)) => r) -> r
instance IsLRPath Nil where
  singPath = SNil
  withIsPath2 r = r
instance (IsLRPath ps) => IsLRPath (L ::: ps) where
  singPath = SL
  withIsPath2 @qs r = withIsPath2 @ps @qs r
instance (IsLRPath ps) => IsLRPath (R ::: ps) where
  singPath = SR
  withIsPath2 @qs r = withIsPath2 @ps @qs r

instance Profunctor (Adj :: CAT (ADJK a b)) where
  dimap = dimapDefault
  r \\ AdjNil = r
  r \\ AdjR f = r \\ f
  r \\ AdjL f = r \\ f
  r \\ AdjCup f = r \\ f
  r \\ AdjCap f = r \\ f
instance Promonad (Adj :: CAT (ADJK a b)) where
  id @ps = go (singPath @(UN AK ps))
    where
      go :: forall ps'. SAdj ps' -> Adj (AK ps') (AK ps')
      go SNil = AdjNil
      go SL = AdjL id
      go SR = AdjR id
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
  type Ob ps = (Is AK ps, IsLRPath (UN AK ps))

-- | The walking adjunction
instance Bicategory ADJK where
  type I = AK Nil
  type ps `O` qs = AK (UN AK qs +++ UN AK ps)
  withOb2 @ps @qs k = withIsPath2 @(UN AK qs) @(UN AK ps) k
  withOb0s r = r
  r \\\ AdjNil = r
  r \\\ AdjR f = r \\\ f
  r \\\ AdjL f = r \\\ f
  r \\\ AdjCup f = r \\\ f
  r \\\ AdjCap f = r \\\ f
  o :: forall {a} {b} (ps :: ADJK a b) qs rs ss. (ps ~> qs) -> (rs ~> ss) -> (ps `O` rs) ~> (qs `O` ss)
  AdjNil `o` f = f \\ f
  f `o` AdjNil = f \\ f
  f `o` AdjR g = AdjR (f `o` g)
  f `o` AdjL g = AdjL (f `o` g)
  f `o` AdjCup g = AdjCup (f `o` g)
  f `o` AdjCap g = AdjCap (f `o` g)
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @p @q @r = obj @p `o` obj @q `o` obj @r
  associatorInv @p @q @r = obj @p `o` obj @q `o` obj @r

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

instance Adjunction_ (AK Nil) (AK Nil) where
  adj = Bi.Adj AdjNil AdjNil

instance Adjunction_ (AK (L ::: Nil)) (AK (R ::: Nil)) where
  adj = Bi.Adj{adjUnit = AdjCap AdjNil, adjCounit = AdjCup AdjNil}

instance Adjunction_ (AK (L ::: R ::: L ::: Nil)) (AK (R ::: L ::: R ::: Nil)) where
  adj = Bi.Adj{adjUnit = AdjCap (AdjCap (AdjCap AdjNil)), adjCounit = AdjCup (AdjCup (AdjCup AdjNil))}

instance Monad (AK (L ::: R ::: Nil)) where
  eta = AdjCap AdjNil
  mu = AdjL (AdjCup (AdjR AdjNil))

instance Comonad (AK (R ::: L ::: Nil)) where
  epsilon = AdjCup AdjNil
  delta = AdjR (AdjCap (AdjL AdjNil))

type SNilOrL :: Path ABK i j -> Type
data SNilOrL p where
  SNilL :: SNilOrL Nil
  SLL :: SNilOrL (L ::: Nil)
type SNilOrR :: Path ABK i j -> Type
data SNilOrR p where
  SNilR :: SNilOrR Nil
  SRR :: SNilOrR (R ::: Nil)

type IsTight :: forall {i} {j}. Path ABK i j -> Constraint
class (IsLRPath ps, IsCotight (CotightAdj ps), Adjunction_ (AK ps) (AK (CotightAdj ps))) => IsTight (ps :: Path ABK i j) where
  type CotightAdj (ps :: Path ABK i j) :: Path ABK j i
  isNilOrL :: SNilOrL ps
instance IsTight Nil where
  type CotightAdj Nil = Nil
  isNilOrL = SNilL
instance IsTight (L ::: Nil) where
  type CotightAdj (L ::: Nil) = R ::: Nil
  isNilOrL = SLL
type IsCotight :: forall {i} {j}. Path ABK i j -> Constraint
class (IsLRPath ps, IsTight (TightAdj ps), Adjunction_ (AK (TightAdj ps)) (AK ps)) => IsCotight (ps :: Path ABK i j) where
  type TightAdj (ps :: Path ABK i j) :: Path ABK j i
  isNilOrR :: SNilOrR ps
instance IsCotight Nil where
  type TightAdj Nil = Nil
  isNilOrR = SNilR
instance IsCotight (R ::: Nil) where
  type TightAdj (R ::: Nil) = L ::: Nil
  isNilOrR = SRR

type instance IsOb Tight (AK ps) = IsTight ps
type instance IsOb Cotight (AK ps) = IsCotight ps
type instance TightAdjoint (AK ps) = AK (TightAdj ps)
type instance CotightAdjoint (AK ps) = AK (CotightAdj ps)
instance WithObO2 Tight ADJK where
  withObO2 @(AK ps) @(AK qs) r = case (isNilOrL @ps, isNilOrL @qs) of
    (SNilL, _) -> r
    (SLL, SNilL) -> r
instance WithObO2 Cotight ADJK where
  withObO2 @(AK ps) @(AK qs) r = case (isNilOrR @ps, isNilOrR @qs) of
    (SNilR, _) -> r
    (SRR, SNilR) -> r
instance Equipment ADJK where
  withTightAdjoint r = r
  withCotightAdjoint r = r
