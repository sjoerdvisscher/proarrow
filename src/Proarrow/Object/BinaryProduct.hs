{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Object.BinaryProduct where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal(..))
import Proarrow.Core (PRO, CategoryOf(..), Promonad (..), Profunctor(..), UN, CAT, Is, dimapDefault)
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Product ((:*:) (..), prod)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Unit qualified as U

infixl 5 &&
infixl 5 &&&
infixl 5 ***

class CategoryOf k => HasBinaryProducts k where
  type (a :: k) && (b :: k) :: k
  fst' :: Obj (a :: k) -> Obj b -> a && b ~> a
  snd' :: Obj (a :: k) -> Obj b -> a && b ~> b
  (&&&) :: (a :: k) ~> x -> a ~> y -> a ~> x && y
  (***) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a && b ~> x && y
  l *** r = (l . fst @a @b) &&& (r . snd @a @b) \\ l \\ r

fst :: forall {k} (a :: k) (b :: k). (HasBinaryProducts k, Ob a, Ob b) => (a && b) ~> a
fst = fst' (obj @a) (obj @b)

snd :: forall {k} (a :: k) (b :: k). (HasBinaryProducts k, Ob a, Ob b) => (a && b) ~> b
snd = snd' (obj @a) (obj @b)


first :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (a && c) ~> (b && c)
first f = f *** obj @c

second :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (c && a) ~> (c && b)
second f = obj @c *** f


type HasProducts k = (HasTerminalObject k, HasBinaryProducts k)

class a ** b ~ a && b => TensorIsProduct a b
instance a ** b ~ a && b => TensorIsProduct a b
class (HasProducts k, Monoidal k, (Unit :: k) ~ TerminalObject, forall (a :: k) (b :: k). TensorIsProduct a b) => Cartesian k
instance (HasProducts k, Monoidal k, (Unit :: k) ~ TerminalObject, forall (a :: k) (b :: k). TensorIsProduct a b) => Cartesian k

instance HasBinaryProducts Type where
  type a && b = (a, b)
  fst' _ _ = P.fst
  snd' _ _ = P.snd
  f &&& g = \a -> (f a, g a)

instance HasBinaryProducts U.UNIT where
  type U.U && U.U = U.U
  fst' U.Unit U.Unit = U.Unit
  snd' U.Unit U.Unit = U.Unit
  U.Unit &&& U.Unit = U.Unit

instance (HasBinaryProducts j, HasBinaryProducts k) => HasBinaryProducts (j, k) where
  type '(a1, a2) && '(b1, b2) = '(a1 && b1, a2 && b2)
  fst' (a1 :**: a2) (b1 :**: b2) = fst' a1 b1 :**: fst' a2 b2
  snd' (a1 :**: a2) (b1 :**: b2) = snd' a1 b1 :**: snd' a2 b2
  (f1 :**: f2) &&& (g1 :**: g2) = (f1 &&& g1) :**: (f2 &&& g2)

instance (CategoryOf j, CategoryOf k) => HasBinaryProducts (PRO j k) where
  type p && q = p :*: q
  fst' Prof{} Prof{} = Prof fstP
  snd' Prof{} Prof{} = Prof sndP
  Prof l &&& Prof r = Prof (prod l r)

leftUnitorProd :: HasProducts k => Obj (a :: k) -> TerminalObject && a ~> a
leftUnitorProd = snd' (obj @TerminalObject)

leftUnitorProdInv :: HasProducts k => Obj (a :: k) -> a ~> TerminalObject && a
leftUnitorProdInv a = terminate' a &&& a

rightUnitorProd :: HasProducts k => Obj (a :: k) -> a && TerminalObject ~> a
rightUnitorProd a = fst' a (obj @TerminalObject)

rightUnitorProdInv :: HasProducts k => Obj (a :: k) -> a ~> a && TerminalObject
rightUnitorProdInv a = a &&& terminate' a

associatorProd :: HasProducts k => Obj (a :: k) -> Obj b -> Obj c -> (a && b) && c ~> a && (b && c)
associatorProd a b c = (fst' a b . fst' (a *** b) c) &&& (snd' a b *** c) \\ (a *** b)

associatorProdInv :: HasProducts k => Obj (a :: k) -> Obj b -> Obj c -> a && (b && c) ~> (a && b) && c
associatorProdInv a b c = (a *** fst' b c) &&& (snd' b c . snd' a (b *** c)) \\ (a *** b)

swapProd :: forall {k} (a :: k) (b :: k). HasBinaryProducts k => Obj a -> Obj b -> (a && b) ~> (b && a)
swapProd a b = snd' a b &&& fst' a b


newtype PROD k = PR k
type instance UN PR (PR k) = k

type Prod :: CAT (PROD k)
data Prod (a :: PROD k) b where
  Prod :: (Ob a, Ob b) => UN PR a ~> UN PR b -> Prod a b

mkProd :: CategoryOf k => (a :: k) ~> b -> Prod (PR a) (PR b)
mkProd f = Prod f \\ f

instance CategoryOf k => Profunctor (Prod :: CAT (PROD k)) where
  dimap = dimapDefault
  r \\ Prod f = r \\ f
instance CategoryOf k => Promonad (Prod :: CAT (PROD k)) where
  id = Prod id
  Prod f . Prod g = Prod (f . g)
instance CategoryOf k => CategoryOf (PROD k) where
  type (~>) = Prod
  type Ob a = (Is PR a, Ob (UN PR a))

instance HasTerminalObject k => HasTerminalObject (PROD k) where
  type TerminalObject = PR TerminalObject
  terminate' (Prod a) = Prod (terminate' a)
instance HasBinaryProducts k => HasBinaryProducts (PROD k) where
  type a && b = PR (UN PR a && UN PR b)
  fst' (Prod a) (Prod b) = mkProd (fst' a b)
  snd' (Prod a) (Prod b) = mkProd (snd' a b)
  Prod f &&& Prod g = mkProd (f &&& g)
  Prod f *** Prod g = mkProd (f *** g)

instance HasProducts k => Monoidal (PROD k) where
  type Unit = TerminalObject
  type a ** b = a && b
  f `par` g = f *** g
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv


instance Monoidal Type where
  type Unit = TerminalObject
  type a ** b = a && b
  f `par` g = f *** g
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance SymMonoidal Type where
  swap' = swapProd

instance Monoidal U.UNIT where
  type Unit = TerminalObject
  type a ** b = a && b
  f `par` g = f *** g
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance SymMonoidal U.UNIT where
  swap' = swapProd
