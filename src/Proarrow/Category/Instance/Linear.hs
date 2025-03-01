{-# LANGUAGE LinearTypes #-}

module Proarrow.Category.Instance.Linear where

import Data.IORef (newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import Data.Void (Void)
import Prelude (Either (..), undefined)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Dual (StarAutonomous (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (RepCostar (..), Representable (..), dimapRep)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Unsafe.Coerce (unsafeCoerce)

data LINEAR = L Type
type instance UN L (L a) = a

type Linear :: CAT LINEAR
data Linear a b where
  Linear :: {unLinear :: a %1 -> b} -> Linear (L a) (L b)

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
  withOb2 r = r
  leftUnitor = Linear \((), x) -> x
  leftUnitorInv = Linear \x -> ((), x)
  rightUnitor = Linear \(x, ()) -> x
  rightUnitorInv = Linear \x -> (x, ())
  associator = Linear \((x, y), z) -> (x, (y, z))
  associatorInv = Linear \(x, (y, z)) -> ((x, y), z)

instance SymMonoidal LINEAR where
  swap = Linear \(x, y) -> (y, x)

-- instance TracedMonoidalProfunctor Linear where
--   trace (Linear f) = Linear \x -> let !(y, u) = f (x, u) in y

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

-- | Forget is a lax monoidal functor
instance MonoidalProfunctor Forget where
  par0 = Forget \() -> ()
  Forget f `par` Forget g = Forget \(x, y) -> (f x, g y)

-- | Forget is also a colax monoidal functor
instance MonoidalProfunctor (RepCostar Forget) where
  par0 = RepCostar id
  RepCostar f `par` RepCostar g = RepCostar \(x, y) -> (f x, g y)

data Ur a where
  Ur :: a -> Ur a

counitUr :: Ur a %1 -> a
counitUr (Ur a) = a

dupUr :: Ur a %1 -> Ur (Ur a)
dupUr (Ur a) = Ur (Ur a)

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

-- | Free is a lax monoidal functor
instance MonoidalProfunctor Free where
  par0 = Free \() -> Ur ()
  Free f `par` Free g = Free \(x, y) -> case (f x, g y) of (Ur a, Ur b) -> Ur (a, b)

-- | Free is also a colax monoidal functor
instance MonoidalProfunctor (RepCostar Free) where
  par0 = RepCostar (Linear (\(Ur _) -> ()))
  RepCostar (Linear f) `par` RepCostar (Linear g) = RepCostar (Linear \(Ur (x, y)) -> (f (Ur x), g (Ur y)))

instance Adjunction Free Forget where
  unit = Forget Ur :.: Free \x -> x
  counit (Free f :.: Forget g) = Linear \a -> case f a of Ur b -> g b

instance HasBinaryCoproducts LINEAR where
  type L a || L b = L (Either a b)
  withObCoprod r = r
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

urWith :: Ur (With a b) %1 -> (Ur a, Ur b)
urWith (Ur (With x f g)) = (Ur (f x), Ur (g x))

instance HasTerminalObject LINEAR where
  type TerminalObject = L Top
  terminate = Linear Top

instance HasBinaryProducts LINEAR where
  type L a && L b = L (With a b)
  withObProd r = r
  fst = Linear \(With x xa _) -> xa x
  snd = Linear \(With x _ xb) -> xb x
  Linear f &&& Linear g = Linear \x -> With x f g

type Not a = a %1 -> ()

not :: (Not b %1 -> Not a) %1 -> a %1 -> b
not nbna a = dn \nb -> nbna nb a

not' :: (a %1 -> b) %1 -> Not b %1 -> Not a
not' ab nb a = nb (ab a)

newtype Par a b = Par (Not (Not a, Not b))

toPar :: (a, b) %1 -> Par a b
toPar (a, b) = Par \(na, nb) -> case (na a, nb b) of ((), ()) -> ()

pairFst :: (a, b `Par` c) %1 -> (a, b) `Par` c
pairFst (a, Par f) = Par \(nab, nc) -> f (\b -> nab (a, b), nc)

pairSnd :: (a `Par` b, c) %1 -> a `Par` (b, c)
pairSnd (Par f, c) = Par \(na, nbc) -> f (na, \b -> nbc (b, c))

parAppL :: (a `Par` b) %1 -> Not a %1 -> b
parAppL (Par f) na = dn \nb -> f (na, nb)

parAppR :: (a `Par` b) %1 -> Not b %1 -> a
parAppR (Par f) nb = dn \na -> f (na, nb)

newtype Quest a = Quest (Not (Ur (Not a)))

notQuest :: Not (Quest a) %1 -> Ur (Not a)
notQuest nqa = dn \nuna -> nqa (Quest nuna)

unitQuest :: a %1 -> Quest a
unitQuest a = Quest \(Ur na) -> na a

multQuest :: Quest (Quest a) %1 -> Quest a
multQuest (Quest f) = Quest \(Ur na) -> f (Ur (\(Quest nuna) -> nuna (Ur na)))

questPar :: Par (Quest a) (Quest b) %1 -> Quest (Either a b)
questPar (Par f) = Quest (\(Ur g) -> f (\(Quest nuna) -> nuna (Ur (\a -> g (Left a))), \(Quest nunb) -> nunb (Ur (\b -> g (Right b)))))

-- LINEAR is not CompactClosed.
instance StarAutonomous LINEAR where
  type Dual (L a) = L (Not a)
  dual (Linear f) = Linear (\nb a -> nb (f a))
  dualInv (Linear f) = Linear (\b -> dn (\na -> f na b))
  linDist (Linear f) = Linear (\a (b, c) -> f (a, b) c)
  linDistInv (Linear f) = Linear (\(a, b) c -> f a (b, c))

-- | Double negation is possible with linear functions, though using `unsafeDupablePerformIO`.
-- Derived from https://gist.github.com/ant-arctica/7563282c57d9d1ce0c4520c543187932
-- TODO: only tested in GHCi, might get ruined by optimizations
dn :: Not (Not a) %1 -> a
dn nna =
  let ref = unsafeDupablePerformIO (newIORef undefined)
  in case nna (unsafeLinear (fill ref)) of () -> unsafeDupablePerformIO (readIORef ref)
  where
    fill ref x = unsafeDupablePerformIO (writeIORef ref x)

unsafeLinear :: (a -> b) %1 -> (a %1 -> b)
unsafeLinear = unsafeCoerce unsafeCoerce

unit :: L () ~> L (Par a (Not a))
unit = Linear \() -> Par \(na, nna) -> nna na

counit :: L (Not a, a) ~> L ()
counit = Linear \(na, a) -> na a


type p !~> q = forall a b. p a b %1 -> q a b

type NegComp :: (j +-> k) -> (i +-> j) -> (i +-> k)
data NegComp p q a c where
  NegComp :: (forall b. Par (p a b) (q b c)) %1 -> NegComp p q a c

newtype Neg p a b = Neg (Not (p b a))

getNeg :: Neg p a b %1 -> Not (p b a)
getNeg (Neg f) = f

conv1 :: NegComp p q !~> Neg (Neg q :.: Neg p)
conv1 (NegComp e) = Neg \(Neg nq :.: Neg np) -> case e of Par e' -> e' (np, nq)

conv2 :: Neg (Neg q :.: Neg p) !~> NegComp p q
conv2 (Neg f) = NegComp (Par (\(np, nq) -> f (Neg nq :.: Neg np)))

asCocat :: (Neg p :.: Neg p !~> Neg p) -> p !~> NegComp p p
asCocat comp p = NegComp (Par \(np1, np2) -> getNeg (comp (Neg np2 :.: Neg np1)) p)