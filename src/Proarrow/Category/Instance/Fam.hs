{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Fam where

import Prelude (($), type (~))

import Proarrow.Category.Instance.Cat (FstCat, Initiate, LftCat, RgtCat, (:|||:), SndCat, (:&&&:), Terminate)
import Proarrow.Category.Instance.Coproduct (COPRODUCT, (:++:) (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Zero (VOID)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), UN, dimapDefault, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:))
import Proarrow.Profunctor.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep, Representable (..), repObj, withRepOb)
import Proarrow.Category.Instance.Unit (Unit(..))
import Proarrow.Profunctor.Constant (Constant)

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
    => (forall s. (Ob s) => (dx % s) ~> (dy % (f % s)))
    -> Fam (DEP x dx :: FAM k) (DEP y dy :: FAM k)

instance (CategoryOf k) => Profunctor (Fam :: CAT (FAM k)) where
  dimap = dimapDefault
  r \\ Fam{} = r

instance (CategoryOf k) => Promonad (Fam :: CAT (FAM k)) where
  id :: forall a x dx. (Ob a, a ~ DEP x dx) => a ~> a
  id = Fam @Id \ @s -> repObj @dx @s
  Fam @f l . Fam @g r = Fam @(f :.: g) \ @s -> withRepOb @g @s $ l @(g % s) . r @s

-- | The Fam construction a.k.a. the free coproduct completion of @k@
instance (CategoryOf k) => CategoryOf (FAM k) where
  type (~>) = Fam
  type Ob (a :: FAM k) = (a ~ DEP (X a) (DX a), Representable (DX a))

data family Embed :: k +-> FAM k
instance (CategoryOf k) => FunctorForRep (Embed :: k +-> FAM k) where
  type Embed @ a = DEP () (Constant a)
  fmap f = Fam @(Constant '()) f \\ f

instance (CategoryOf k) => HasInitialObject (FAM k) where
  type InitialObject = DEP VOID (Rep Initiate)
  initiate = Fam @(Rep Initiate) \ @s -> case obj @s of {}

instance (CategoryOf k) => HasBinaryCoproducts (FAM k) where
  type a || b = DEP (COPRODUCT (X a) (X b)) (DX a :|||: DX b)
  withObCoprod r = r
  lft :: forall (a :: FAM k) b. (Ob a, Ob b) => a ~> (a || b)
  lft = Fam @LftCat \ @s -> repObj @(DX a) @s
  rgt :: forall (a :: FAM k) b. (Ob a, Ob b) => b ~> (a || b)
  rgt = Fam @RgtCat \ @s -> repObj @(DX b) @s
  (|||) :: forall (a :: FAM k) (x :: FAM k) (y :: FAM k). (x ~> a) -> (y ~> a) -> (x || y) ~> a
  Fam @f l ||| Fam @g r = Fam @(f :|||: g) \ @s -> case obj @s of
    InjL @_ @s' s -> l @s' \\ s
    InjR @_ @s' s -> r @s' \\ s

data family Term :: () +-> k
instance (HasTerminalObject k) => FunctorForRep (Term :: () +-> k) where
  type Term @ '() = TerminalObject
  fmap Unit = id
instance (HasTerminalObject k) => HasTerminalObject (FAM k) where
  type TerminalObject = DEP () (Rep Term)
  terminate @a = Fam @(Rep Terminate) \ @s -> withRepOb @(DX a) @s terminate

data family (l :: x +-> k) :&&: (r :: y +-> k) :: (x, y) +-> k
instance (Representable (l :: x +-> k), Representable r, HasBinaryProducts k) => FunctorForRep (l :&&: r) where
  type (l :&&: r) @ '(a, b) = (l % a) && (r % b)
  fmap (s1 :**: s2) = repMap @l s1 *** repMap @r s2
instance (HasBinaryProducts k) => HasBinaryProducts (FAM k) where
  type a && b = DEP (X a, X b) (Rep (DX a :&&: DX b))
  withObProd r = r
  fst :: forall (a :: FAM k) b. (Ob a, Ob b) => (a && b) ~> a
  fst = Fam @FstCat \ @'(l, r) -> withRepOb @(DX a) @l $ withRepOb @(DX b) @r $ fst @_ @(DX a % l) @(DX b % r)
  snd :: forall (a :: FAM k) b. (Ob a, Ob b) => (a && b) ~> b
  snd = Fam @SndCat \ @'(l, r) -> withRepOb @(DX a) @l $ withRepOb @(DX b) @r $ snd @_ @(DX a % l) @(DX b % r)
  (&&&) :: forall (a :: FAM k) (x :: FAM k) (y :: FAM k). (a ~> x) -> (a ~> y) -> a ~> (x && y)
  Fam @f l &&& Fam @g r = Fam @(f :&&&: g) \ @s -> l @s &&& r @s