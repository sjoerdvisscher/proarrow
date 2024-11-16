{-# LANGUAGE LinearTypes #-}

module Proarrow.Category.Instance.Linear where

import Data.Kind (Type)
import Data.Void (Void)
import Prelude (Either (..))

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid (..))

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

instance MonoidalProfunctor Linear where
  par0 = id
  Linear f `par` Linear g = Linear \(x, y) -> (f x, g y)

instance Monoidal LINEAR where
  type Unit = L ()
  type L a ** L b = L (a, b)
  leftUnitor (Linear f) = Linear \((), x) -> f x
  leftUnitorInv (Linear f) = Linear \x -> ((), f x)
  rightUnitor (Linear f) = Linear \(x, ()) -> f x
  rightUnitorInv (Linear f) = Linear \x -> (f x, ())
  associator Linear{} Linear{} Linear{} = Linear \((x, y), z) -> (x, (y, z))
  associatorInv Linear{} Linear{} Linear{} = Linear \(x, (y, z)) -> ((x, y), z)

instance SymMonoidal LINEAR where
  swap' (Linear f) (Linear g) = Linear \(x, y) -> (g y, f x)

instance Closed LINEAR where
  type a ~~> b = L (UN L a %1 -> UN L b)
  curry' Linear{} Linear{} (Linear f) = Linear \a b -> f (a, b)
  uncurry' Linear{} Linear{} (Linear f) = Linear \(a, b) -> f a b
  Linear f ^^^ Linear g = Linear \h x -> f (h (g x))

type Forget :: LINEAR +-> Type
data Forget a b where
  Forget :: (a -> b) -> Forget a (L b)
instance Profunctor Forget where
  dimap = dimapRep
  r \\ Forget{} = r
instance Representable Forget where
  type Forget % a = UN L a
  index (Forget f) = f
  tabulate = Forget
  repMap (Linear f) x = f x
instance MonoidalProfunctor Forget where
  par0 = Forget \() -> ()
  Forget f `par` Forget g = Forget \(x, y) -> (f x, g y)

data Ur a where
  Ur :: a -> Ur a

instance Functor Ur where
  map f (Ur a) = Ur (f a)

instance Comonoid (L (Ur a)) where
  counit = Linear \(Ur _) -> ()
  comult = Linear \(Ur a) -> (Ur a, Ur a)

type Free :: Type +-> LINEAR
data Free a b where
  Free :: (a %1 -> Ur b) -> Free (L a) b
instance Profunctor Free where
  dimap = dimapRep
  r \\ Free{} = r
instance Representable Free where
  type Free % a = L (Ur a)
  index (Free f) = Linear f
  tabulate (Linear f) = Free f
  repMap f = Linear \(Ur a) -> Ur (f a)
instance MonoidalProfunctor Free where
  par0 = Free \() -> Ur ()
  Free f `par` Free g = Free \(x, y) -> case (f x, g y) of (Ur a, Ur b) -> Ur (a, b)

unlift2Free :: Free % (x ** y) ~> (Free % x) ** (Free % y)
unlift2Free = Linear \(Ur (x, y)) -> (Ur x, Ur y)

unlift2Forget :: (Ob x, Ob y) => Forget % (x ** y) ~> (Forget % x) ** (Forget % y)
unlift2Forget = id

instance Adjunction Free Forget where
  unit = Forget Ur :.: Free \x -> x
  counit (Free f :.: Forget g) = Linear \a -> case f a of Ur b -> g b

instance HasBinaryCoproducts LINEAR where
  type L a || L b = L (Either a b)
  lft = Linear Left
  rgt = Linear Right
  Linear f ||| Linear g = Linear \case
    Left x -> f x
    Right y -> g y

instance HasInitialObject LINEAR where
  type InitialObject = L Void
  initiate = Linear \case {}

data Top where
  Top :: a %1 -> Top

data With a b where
  With :: x %1 -> (x %1 -> a) -> (x %1 -> b) -> With a b

instance HasTerminalObject LINEAR where
  type TerminalObject = L Top
  terminate = Linear Top

instance HasBinaryProducts LINEAR where
  type L a && L b = L (With a b)
  fst = Linear \(With x xa _) -> xa x
  snd = Linear \(With x _ xb) -> xb x
  Linear f &&& Linear g = Linear \x -> With x f g