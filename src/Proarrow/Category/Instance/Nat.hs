{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Nat where

import Data.Functor.Compose (Compose (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Sum (Sum (..))
import Data.Kind (Type)
import Data.Void (Void, absurd)

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, (//))
import Proarrow.Functor (Functor (..), type (.~>))
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), PROD (..), Prod (..))
import Proarrow.Object.Coexponential (Coclosed (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))

type Nat :: CAT (j -> k)
data Nat f g where
  Nat
    :: (Functor f, Functor g)
    => {unNat :: f .~> g}
    -> Nat f g

(!) :: Nat f g -> a ~> b -> f a ~> g b
Nat f ! ab = f . map ab \\ ab

instance CategoryOf (k1 -> Type) where
  type (~>) = Nat
  type Ob f = Functor f

instance Promonad (Nat :: CAT (j -> Type)) where
  id = n
    where
      n :: forall f. (Functor f) => Nat f f
      n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> Type)) where
  dimap = dimapDefault
  r \\ Nat{} = r

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
  uncurry (Prod (Nat n)) = Prod (Nat \(Pair f g) -> case n f of Exp k -> k id g)
  Prod (Nat m) ^^^ Prod (Nat n) = Prod (Nat \(Exp k) -> Exp \cd h -> m (k cd (n h)) \\ cd)

instance MonoidalProfunctor (Nat :: CAT (Type -> Type)) where
  par0 = id
  Nat n `par` Nat m = Nat (\(Compose fg) -> Compose (n (map m fg)))

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
  unitor = runIdentity
  unitorInv = Identity
  multiplicator = Compose
  multiplicatorInv = getCompose

newtype HaskRan j h a = Ran {runRan :: forall b. (a -> j b) -> h b}
instance Functor (HaskRan j h) where
  map f (Ran k) = Ran \j -> k (j . f)
instance Closed (Type -> Type) where
  type j ~~> h = HaskRan j h
  withObExp r = r
  curry (Nat n) = Nat \fa -> Ran \ajb -> n (Compose (map ajb fa))
  uncurry (Nat n) = Nat \(Compose fja) -> runRan (n fja) id
  (^^^) (Nat by) (Nat xa) = Nat \h -> Ran \x -> by (runRan h (xa . x))

data HaskLan j f a where
  Lan :: (j b -> a) -> f b -> HaskLan j f a
instance Functor (HaskLan j f) where
  map g (Lan k f) = Lan (g . k) f
instance Coclosed (Type -> Type) where
  type f <~~ j = HaskLan j f
  withObCoExp r = r
  coeval = Nat (Compose . Lan id)
  coevalUniv (Nat n) = Nat \(Lan k f) -> map k (getCompose (n f))

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
