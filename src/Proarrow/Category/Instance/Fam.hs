{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Fam where

import Data.Kind (Type)
import GHC.Base (Any)
import Prelude (type (~))

import Proarrow.Category.Instance.Coproduct (COPRODUCT (..), Codiag, Lft, Rgt, (:++:) (..))
import Proarrow.Category.Instance.Product (Diag, Fst, Snd, (:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Category.Opposite (OPPOSITE)
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , UN
  , dimapDefault
  , lmap
  , obj
  , rmap
  , tgt
  , (//)
  , (:~>)
  , type (+->)
  )
import Proarrow.Functor (FunctorForRep (..), Presheaf)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Constant (Constant)
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), repUniv)
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))

type data FAM (k :: Kind) = forall (x :: Kind). DEP_ (x +-> k)
type instance UN DEP_ (DEP_ dx) = dx

type family X (a :: FAM k) :: Kind where
  X (DEP_ (dx :: x +-> k)) = x
type DX :: forall (a :: FAM k) -> (X a +-> k)
type DX a = UN DEP_ a

type DEP :: forall x -> (x +-> k) -> FAM k
type DEP x dx = DEP_ dx

type Fam :: CAT (FAM k)
data Fam a b where
  Fam
    :: forall {k} {x} {y} {dx :: x +-> k} {dy :: y +-> k} (f :: x +-> y)
     . (Representable dx, Representable dy, Representable f)
    => dx :~> dy :.: f
    -> Fam (DEP x dx :: FAM k) (DEP y dy :: FAM k)

instance (CategoryOf k) => Profunctor (Fam :: CAT (FAM k)) where
  dimap = dimapDefault
  r \\ Fam{} = r

instance (CategoryOf k) => Promonad (Fam :: CAT (FAM k)) where
  id = Fam @Id \dx -> dx :.: Id (tgt dx)
  Fam @f l . Fam @g r = Fam @(f :.: g) \dx -> case r dx of dy :.: g -> case l dy of dz :.: f -> dz :.: (f :.: g)

-- | The Fam construction a.k.a. the free coproduct completion of @k@
instance (CategoryOf k) => CategoryOf (FAM k) where
  type (~>) = Fam
  type Ob (a :: FAM k) = (a ~ DEP (X a) (DX a), Representable (DX a))

data family Embed :: k +-> FAM k
instance (CategoryOf k) => FunctorForRep (Embed :: k +-> FAM k) where
  type Embed @ a = DEP () (Rep (Constant a))
  fmap f = f // Fam @(Rep (Constant '())) \(Rep a) -> Rep (f . a) :.: Rep Unit

type AsPresheaf :: x +-> k -> Presheaf k
data AsPresheaf dx a u where
  AsPresheaf :: dx a b -> AsPresheaf dx a '()
instance (CategoryOf k, Profunctor dx) => Profunctor (AsPresheaf dx :: Presheaf k) where
  dimap l Unit (AsPresheaf dx) = AsPresheaf (lmap l dx)
  r \\ AsPresheaf dx = r \\ dx
data family IsPresheafSub :: FAM k +-> Presheaf k
instance (CategoryOf k) => FunctorForRep (IsPresheafSub :: FAM k +-> Presheaf k) where
  type IsPresheafSub @ (DEP x dx) = AsPresheaf dx
  fmap (Fam r) = Prof \(AsPresheaf dx) -> AsPresheaf (case r dx of dy :.: f -> rmap (index f) dy)

data family Initiate :: VOID +-> k
instance (CategoryOf k) => FunctorForRep (Initiate :: VOID +-> k) where
  type Initiate @ a = Any
  fmap = \case {}

instance (CategoryOf k) => HasInitialObject (FAM k) where
  type InitialObject = DEP VOID (Rep Initiate)
  initiate = Fam @(Rep Initiate) \(Rep @_ @_ @b _) -> case obj @b of {}

instance (CategoryOf k) => HasBinaryCoproducts (FAM k) where
  type a || b = DEP (COPRODUCT (X a) (X b)) (Rep Codiag :.: (DX a :++: DX b))
  withObCoprod r = r
  lft = Fam @(Rep Lft) \p -> (repUniv :.: InjL p) :.: repUniv \\ p
  rgt = Fam @(Rep Rgt) \q -> (repUniv :.: InjR q) :.: repUniv \\ q
  Fam @f l ||| Fam @g r = Fam @(Rep Codiag :.: (f :++: g)) \case
    Rep d :.: InjL p -> case l p of dx :.: f -> lmap d dx :.: (repUniv :.: InjL f) \\ f
    Rep d :.: InjR q -> case r q of dy :.: g -> lmap d dy :.: (repUniv :.: InjR g) \\ g

instance (HasTerminalObject k) => HasTerminalObject (FAM k) where
  type TerminalObject = DEP () TerminalProfunctor
  terminate = Fam @(Rep (Constant '())) \dx -> TerminalProfunctor :.: Rep Unit \\ dx

instance (HasBinaryProducts k) => HasBinaryProducts (FAM k) where
  type a && b = DEP (X a, X b) (Corep Diag :.: (DX a :**: DX b))
  withObProd r = r
  fst = Fam @(Rep Fst) \(Corep (d :**: _) :.: (l :**: r)) -> lmap d l :.: repUniv \\ l \\ r
  snd = Fam @(Rep Snd) \(Corep (_ :**: d) :.: (l :**: r)) -> lmap d r :.: repUniv \\ l \\ r
  Fam @f l &&& Fam @g r = Fam @((f :**: g) :.: Rep Diag) \dx -> case (l dx, r dx) of
    (dy1 :.: f, dy2 :.: g) -> (corepUniv :.: (dy1 :**: dy2)) :.: ((f :**: g) :.: repUniv) \\ f \\ dy2

type Poly = FAM (OPPOSITE Type)