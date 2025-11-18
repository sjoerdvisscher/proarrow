{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Fam where

import Data.Kind (Type)
import Prelude (($), type (~))

import Proarrow.Category.Instance.Cat (FstCat, Initiate, LftCat, RgtCat, SndCat, Terminate, (:&&&:) (..), (:|||:) (..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT)
import Proarrow.Category.Instance.Product ((:**:) (..))
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
import Proarrow.Profunctor.Constant (Constant (..))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..), trivialRep, withRepOb)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))

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
  type Embed @ a = DEP () (Constant a)
  fmap f = f // Fam @(Constant '()) \(Constant a) -> Constant (f . a) :.: Constant Unit

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

instance (CategoryOf k) => HasInitialObject (FAM k) where
  type InitialObject = DEP VOID (Rep Initiate)
  initiate = Fam @(Rep Initiate) \(Rep @_ @_ @b _) -> case obj @b of {}

instance (CategoryOf k) => HasBinaryCoproducts (FAM k) where
  type a || b = DEP (COPRODUCT (X a) (X b)) (DX a :|||: DX b)
  withObCoprod r = r
  lft = Fam @(Rep LftCat) \p -> InjLP p :.: trivialRep \\ p
  rgt = Fam @(Rep RgtCat) \q -> InjRP q :.: trivialRep \\ q
  Fam @f l ||| Fam @g r = Fam @(f :|||: g) \case
    InjLP p -> case l p of dx :.: f -> dx :.: InjLP f
    InjRP q -> case r q of dy :.: g -> dy :.: InjRP g

type Term :: () +-> k
data Term a b where Term :: Ob a => Term a '()
instance (CategoryOf k) => Profunctor (Term :: () +-> k) where
  dimap l Unit Term = Term \\ l
  r \\ Term = r
instance (HasTerminalObject k) => Representable (Term :: () +-> k) where
  type Term % '() = TerminalObject
  tabulate f = Term \\ f
  index Term = terminate
  repMap Unit = id
instance (CategoryOf k) => Corepresentable (Term :: () +-> k) where
  type Term %% a = '()
  cotabulate Unit = Term
  coindex Term = Unit
  corepMap _ = Unit
instance (HasTerminalObject k) => HasTerminalObject (FAM k) where
  type TerminalObject = DEP () Term
  terminate = Fam @(Rep Terminate) \dx -> Term :.: Rep Unit \\ dx

type (:&&:) :: x +-> k -> y +-> k -> (x, y) +-> k
data (p :&&: q) a b where
  (:&&:) :: p a b -> q a c -> (p :&&: q) a '(b, c)
instance (Profunctor l, Profunctor r, CategoryOf k) => Profunctor (l :&&: r :: (x, y) +-> k) where
  dimap l (r0 :**: r1) (p :&&: q) = dimap l r0 p :&&: dimap l r1 q
  r \\ (p :&&: q) = r \\ p \\ q
instance (Representable l, Representable r, HasBinaryProducts k) => Representable (l :&&: r :: (x, y) +-> k) where
  type (l :&&: r) % '(a, b) = (l % a) && (r % b)
  tabulate @'(a, b) f = withRepOb @l @a $ withRepOb @r @b $ tabulate (fst @_ @(l % a) @(r % b) . f) :&&: tabulate (snd @_ @(l % a) @(r % b) . f)
  index (p :&&: q) = index p &&& index q
  repMap (f :**: g) = repMap @l f *** repMap @r g
instance (Corepresentable l, Corepresentable r, CategoryOf k) => Corepresentable (l :&&: r :: (x, y) +-> k) where
  type (l :&&: r) %% a = '(l %% a, r %% a)
  cotabulate (f :**: g) = cotabulate f :&&: cotabulate g
  coindex (p :&&: q) = coindex p :**: coindex q
  corepMap f = corepMap @l f :**: corepMap @r f
instance (HasBinaryProducts k) => HasBinaryProducts (FAM k) where
  type a && b = DEP (X a, X b) (DX a :&&: DX b)
  withObProd r = r
  fst = Fam @(Rep FstCat) \(l :&&: r) -> l :.: Rep id \\ l \\ r
  snd = Fam @(Rep SndCat) \(l :&&: r) -> r :.: Rep id \\ l \\ r
  Fam @f l &&& Fam @g r = Fam @(f :&&&: g) \dx -> case (l dx, r dx) of (dy1 :.: f, dy2 :.: g) -> (dy1 :&&: dy2) :.: (f :&&&: g)

type Poly = FAM (OPPOSITE Type)