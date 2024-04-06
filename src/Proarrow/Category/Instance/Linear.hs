{-# LANGUAGE LinearTypes #-}
module Proarrow.Category.Instance.Linear where

import Data.Kind (Type)
import Data.Void (Void)
import Prelude (Either(..))

import Proarrow.Core (UN, Is, CAT, Profunctor (..), dimapDefault, Promonad (..), CategoryOf(..), PRO)
import Proarrow.Category.Monoidal (Monoidal(..), SymMonoidal (..), MonoidalProfunctor (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable(..))
import Proarrow.Adjunction (Adjunction(..))
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Object.Exponential (Closed(..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts(..))
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Functor (Functor(..))


type data LINEAR = L Type
type instance UN L (L a) = a

type Linear :: CAT LINEAR
data Linear a b where
  Linear :: (a %1 -> b) -> Linear (L a) (L b)

instance Profunctor Linear where
  dimap = dimapDefault
  r \\ Linear{} = r
instance Promonad Linear where
  id = Linear \x -> x
  Linear f . Linear g = Linear \x -> f (g x)
-- | Category of linear functions.
instance CategoryOf LINEAR where
  type (~>) = Linear
  type Ob (a :: LINEAR) = Is L a

instance Monoidal LINEAR where
  type Unit = L ()
  type L a ** L b = L (a, b)
  Linear f `par` Linear g = Linear \(x, y) -> (f x, g y)
  leftUnitor (Linear f) = Linear \((), x) -> f x
  leftUnitorInv (Linear f) = Linear \x -> ((), f x)
  rightUnitor (Linear f) = Linear \(x, ()) -> f x
  rightUnitorInv (Linear f) = Linear \x -> (f x, ())
  associator Linear{} Linear{} Linear{} = Linear \((x, y), z) -> (x, (y, z))
  associatorInv Linear{} Linear{} Linear{} = Linear \(x, (y, z)) -> ((x, y), z)

instance SymMonoidal LINEAR where
  swap' Linear{} Linear{} = Linear \(x, y) -> (y, x)

instance Closed LINEAR where
  type a ~~> b = L (UN L a %1 -> UN L b)
  curry' Linear{} Linear{} (Linear f) = Linear \a b -> f (a, b)
  uncurry' Linear{} Linear{} (Linear f) = Linear \(a, b) -> f a b
  Linear f ^^^ Linear g = Linear \h x -> f (h (g x))


type Forget :: PRO LINEAR Type
data Forget a b where
  Forget :: (a -> b) -> Forget (L a) b
instance Profunctor Forget where
  dimap (Linear f) g (Forget h) = Forget \x -> g (h (f x))
  r \\ Forget{} = r
instance Corepresentable Forget where
  type Forget %% a = UN L a
  coindex (Forget f) = f
  cotabulate = Forget
  corepMap (Linear f) x = f x
instance MonoidalProfunctor Forget where
  lift0 = Forget \() -> ()
  lift2 (Forget f) (Forget g) = Forget \(x, y) -> (f x, g y)


data Ur a where
  Ur :: a -> Ur a

unur :: Ur a %1 -> a
unur (Ur a) = a

instance Functor Ur where
  map f (Ur a) = Ur (f a)

type Free :: PRO Type LINEAR
data Free a b where
  Free :: (Ur a %1 -> b) -> Free a (L b)
instance Profunctor Free where
  dimap f (Linear g) (Free h) = Free \(Ur x) -> g (h (Ur (f x)))
  r \\ Free{} = r
instance Corepresentable Free where
  type Free %% a = L (Ur a)
  coindex (Free f) = Linear f
  cotabulate (Linear f) = Free f
  corepMap f = Linear \(Ur a) -> Ur (f a)
instance MonoidalProfunctor Free where
  lift0 = Free \(Ur ()) -> ()
  lift2 (Free f) (Free g) = Free \(Ur (x, y)) -> (f (Ur x), g (Ur y))

unlift2Free :: Free %% (x ** y) ~> (Free %% x) ** (Free %% y)
unlift2Free = Linear \(Ur (x, y)) -> (Ur x, Ur y)

unlift2Forget :: (Ob x, Ob y) => Forget %% (x ** y) ~> (Forget %% x) ** (Forget %% y)
unlift2Forget = id


instance Adjunction Free Forget where
  unit = Forget id :.: Free unur
  counit (Free f :.: Forget g) a = g (f (Ur a))


instance HasBinaryCoproducts LINEAR where
  type L a || L b = L (Either a b)
  lft' Linear{} Linear{} = Linear Left
  rgt' Linear{} Linear{} = Linear Right
  Linear f ||| Linear g = Linear \case
    Left x -> f x
    Right y -> g y

instance HasInitialObject LINEAR where
  type InitialObject = L Void
  initiate' Linear{} = Linear \case