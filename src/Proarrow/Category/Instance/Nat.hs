{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Nat where

import Data.Bifunctor qualified as P
import Data.Functor.Compose (Compose (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Sum (Sum (..))
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude qualified as P

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, (//))
import Proarrow.Functor (Functor (..), type (.~>))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), PROD (..), Prod (..))
import Proarrow.Object.Coexponential (Coclosed (..))
import Proarrow.Object.Copower (Copowered (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Power (Powered (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))

type Nat :: CAT (j -> k)
data Nat f g where
  Nat
    :: (Functor f, Functor g)
    => {unNat :: f .~> g}
    -> Nat f g

(!) :: Nat f g -> a ~> b -> f a ~> g b
Nat f ! ab = f . map ab \\ ab

-- | The category of functors with target category Hask.
instance CategoryOf (k1 -> Type) where
  type (~>) = Nat
  type Ob f = Functor f

instance Promonad (Nat :: CAT (j -> Type)) where
  id @f = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> Type)) where
  dimap = dimapDefault
  r \\ Nat{} = r

instance Functor (:.:) where
  map (Prof n) = Nat (Prof \(p :.: q) -> n p :.: q)

instance (CategoryOf k1) => HasTerminalObject (k1 -> Type) where
  type TerminalObject = Const ()
  terminate = Nat \_ -> Const ()

instance (CategoryOf k1) => HasInitialObject (k1 -> Type) where
  type InitialObject = Const Void
  initiate = Nat \(Const v) -> absurd v

instance (Functor f, Functor g) => Functor (Product f g) where
  map f (Pair x y) = Pair (map f x) (map f y)

instance HasBinaryProducts (k1 -> Type) where
  type f && g = Product f g
  withObProd r = r
  fst = Nat \(Pair f _) -> f
  snd = Nat \(Pair _ g) -> g
  Nat f &&& Nat g = Nat \a -> Pair (f a) (g a)

instance (Functor f, Functor g) => Functor (Sum f g) where
  map f (InL x) = InL (map f x)
  map f (InR y) = InR (map f y)

instance HasBinaryCoproducts (k1 -> Type) where
  type f || g = Sum f g
  withObCoprod r = r
  lft = Nat InL
  rgt = Nat InR
  Nat f ||| Nat g = Nat \case
    InL x -> f x
    InR y -> g y

data (f :~>: g) a where
  Exp :: (Ob a) => (forall b. a ~> b -> f b -> g b) -> (f :~>: g) a

instance (Functor f, Functor g) => Functor (f :~>: g) where
  map ab (Exp k) = ab // Exp \bc fc -> k (bc . ab) fc

instance (CategoryOf k1) => Closed (PROD (k1 -> Type)) where
  type f ~~> g = PR (UN PR f :~>: UN PR g)
  withObExp r = r
  curry (Prod (Nat n)) = Prod (Nat \f -> Exp \ab g -> n (Pair (map ab f) g) \\ ab)
  apply = Prod (Nat \(Pair (Exp k) g) -> k id g)
  Prod (Nat m) ^^^ Prod (Nat n) = Prod (Nat \(Exp k) -> Exp \cd h -> m (k cd (n h)) \\ cd)

instance MonoidalProfunctor (Nat :: CAT (Type -> Type)) where
  par0 = id
  Nat n `par` Nat m = Nat (\(Compose fg) -> Compose (n (map m fg)))

-- | Composition as monoidal tensor.
instance Monoidal (Type -> Type) where
  type Unit = Identity
  type f ** g = Compose f g
  withOb2 r = r
  leftUnitor = Nat (runIdentity . getCompose)
  leftUnitorInv = Nat (Compose . Identity)
  rightUnitor = Nat (map runIdentity . getCompose)
  rightUnitorInv = Nat (Compose . map Identity)
  associator = Nat (Compose . map Compose . getCompose . getCompose)
  associatorInv = Nat (Compose . Compose . map getCompose . getCompose)

instance Strong (Type -> Type) (->) where
  act (Nat n) f = n . map f
instance MonoidalAction (Type -> Type) Type where
  type Act (p :: Type -> Type) (x :: Type) = p x
  withObAct r = r
  unitor = runIdentity
  unitorInv = Identity
  multiplicator = Compose
  multiplicatorInv = getCompose

type Ran :: (j -> k) -> (j -> Type) -> k -> Type
newtype Ran j h a = Ran {runRan :: forall b. (a ~> j b) -> h b}
instance (CategoryOf k) => Functor (Ran j h :: k -> Type) where
  map f (Ran k) = Ran \j -> k (j . f)
instance Closed (Type -> Type) where
  type j ~~> h = Ran j h
  withObExp r = r
  curry (Nat n) = Nat \fa -> Ran \ajb -> n (Compose (map ajb fa))
  apply = Nat \(Compose fja) -> runRan fja id
  (^^^) (Nat by) (Nat xa) = Nat \h -> Ran \x -> by (runRan h (xa . x))

type Lan :: (j -> k) -> (j -> Type) -> k -> Type
data Lan j f a where
  Lan :: (j b ~> a) -> f b -> Lan j f a
instance (CategoryOf k) => Functor (Lan j f :: k -> Type) where
  map g (Lan k f) = Lan (g . k) f
instance Coclosed (Type -> Type) where
  type f <~~ j = Lan j f
  withObCoExp r = r
  coeval = Nat (Compose . Lan id)
  coevalUniv (Nat n) = Nat \(Lan k f) -> map k (getCompose (n f))

data (f :^: n) a where
  Power :: (Ob a) => {unPower :: n -> f a} -> (f :^: n) a
instance (Functor f) => Functor (f :^: n) where
  map g (Power k) = g // Power \n -> map g (k n)
instance Powered Type (k -> Type) where
  type f ^ n = f :^: n
  withObPower r = r
  power f = Nat \g -> Power \n -> unNat (f n) g
  unpower (Nat f) n = Nat \g -> unPower (f g) n

data (n :*.: f) a where
  Copower :: (Ob a) => {unCopower :: (n, f a)} -> (n :*.: f) a
instance (Functor f) => Functor (n :*.: f) where
  map g (Copower (n, f)) = g // Copower (n, map g f)
instance Copowered Type (k -> Type) where
  type n *. f = n :*.: f
  withObCopower r = r
  copower f = Nat \(Copower (n, g)) -> unNat (f n) g
  uncopower (Nat f) n = Nat \p -> f (Copower (n, p))

data CatAsComonoid k a where
  CatAsComonoid :: forall {k} (c :: k) a. (Ob c) => (forall c'. c ~> c' -> a) -> CatAsComonoid k a
instance Functor (CatAsComonoid k) where
  map f (CatAsComonoid k) = CatAsComonoid (f . k)

instance (CategoryOf k) => Comonoid (CatAsComonoid k) where
  counit = Nat \(CatAsComonoid k) -> Identity (k id)
  comult = Nat \(CatAsComonoid @a k) ->
    Compose
      ( CatAsComonoid @a
          \(f :: a ~> b) ->
            f // CatAsComonoid @b
              \g -> k (g . f)
      )

data ComonoidAsCat (w :: Type -> Type) a b where
  ComonoidAsCat :: (w a -> b) -> ComonoidAsCat w a b

instance (Functor w) => Profunctor (ComonoidAsCat w) where
  dimap f g (ComonoidAsCat h) = ComonoidAsCat (g . h . map f)

instance (Comonoid w) => Promonad (ComonoidAsCat w) where
  id = ComonoidAsCat (runIdentity . unNat counit)
  ComonoidAsCat f . ComonoidAsCat g = ComonoidAsCat (f . map g . getCompose . unNat comult)

-- | The category of functors with target category @k2 -> k3 -> Type@.
-- Note that @CategoryOf (k1 -> k2 -> Type)@ is reserved for profunctors.
instance CategoryOf (k1 -> k2 -> k3 -> Type) where
  type (~>) = Nat
  type Ob f = Functor f

instance Promonad (Nat :: CAT (k1 -> k2 -> k3 -> Type)) where
  id = n
    where
      n :: forall f. (Functor f) => Nat f f
      n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> k2 -> k3 -> Type)) where
  dimap f g h = g . h . f
  r \\ Nat{} = r

-- | The category of functors with target category k2 -> k3 -> k4 -> Type.
instance CategoryOf (k1 -> k2 -> k3 -> k4 -> Type) where
  type (~>) = Nat
  type Ob f = Functor f

instance Promonad (Nat :: CAT (k1 -> k2 -> k3 -> k4 -> Type)) where
  id = n
    where
      n :: forall f. (Functor f) => Nat f f
      n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> k2 -> k3 -> k4 -> Type)) where
  dimap f g h = g . h . f
  r \\ Nat{} = r

newtype NatK j k = NT (j -> k)
type instance UN NT (NT f) = f

data Nat' f g where
  Nat'
    :: (Functor f, Functor g)
    => {unNat' :: f .~> g}
    -> Nat' (NT f) (NT g)

-- | The category of functors and natural transformations.
instance CategoryOf (NatK j k) where
  type (~>) = Nat'
  type Ob f = (Is NT f, Functor (UN NT f))

instance Promonad (Nat' :: CAT (NatK j k)) where
  id = n
    where
      n :: forall f. (Functor f) => Nat' (NT f) (NT f)
      n = Nat' (map @f id)
  Nat' f . Nat' g = Nat' (f . g)

instance Profunctor (Nat' :: CAT (NatK j k)) where
  dimap = dimapDefault
  r \\ Nat'{} = r

instance Functor P.Either where map f = Nat (P.first f)
instance Functor (,) where map f = Nat (P.first f)

first :: (Functor f, Ob c) => (a ~> b) -> f a c -> f b c
first f = unNat (map f)

bimap :: (Functor f, Functor (f a)) => a ~> c -> b ~> d -> f a b -> f c d
bimap l r = first l . map r \\ l \\ r