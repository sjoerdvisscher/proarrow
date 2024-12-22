{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory
  ( -- * Bicategories
    Bicategory (..)
  , (==)
  , (||)
  , appendObj
  , leftUnitor'
  , leftUnitorInv'
  , rightUnitor'
  , rightUnitorInv'
  , associator'
  , associatorInv'
  , leftUnitorWith
  , leftUnitorInvWith
  , rightUnitorWith
  , rightUnitorInvWith
  , Ob0'
  , Ob'

    -- * More
  , Monad (..)
  , Comonad (..)
  , Adjunction (..)
  , leftAdjunct
  , rightAdjunct
  , Bimodule (..)
  )
where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), id)
import Proarrow.Object (Obj, obj)

infixl 8 ||
infixl 7 ==
infixl 1 \\\

-- | A bicategory is locally "something" if each hom-category is "something".
class (forall j k. (Ob0 kk j, Ob0 kk k) => c (kk j k)) => Locally c kk

instance (forall j k. (Ob0 kk j, Ob0 kk k) => c (kk j k)) => Locally c kk

class (Ob0 kk j) => Ob0' kk j
instance (Ob0 kk j) => Ob0' kk j

class (Ob0 kk j, Ob0 kk k, Ob a) => Ob' (a :: kk j k)
instance (Ob0 kk j, Ob0 kk k, Ob a) => Ob' (a :: kk j k)

-- | Bicategories.
--
-- * 0-cells are kinds @i@, @j@, @k@... satisfying the @Ob0 kk@ constraint.
-- * 1-cells are types of kind @kk j k@ for any 0-cells @j@ and @k@, satisfying the @Ob@ constraint.
-- * 2-cells are values of type @p ~> q@, where @p@ and @q@ are 1-cells.
type Bicategory :: forall {s}. CAT s -> Constraint
class (Locally CategoryOf kk, CategoryOf s) => Bicategory (kk :: CAT s) where
  type Ob0 kk (j :: k) :: Constraint
  type Ob0 kk j = ()
  type I :: kk i i
  type O (p :: kk j k) (q :: kk i j) :: kk i k

  -- | The identity 1-cell (as represented by an identity 2-cell).
  iObj :: (Ob0 kk i) => Obj (I :: kk i i)
  default iObj :: (Ob0 kk i, Ob (I :: kk i i)) => Obj (I :: kk i i)
  iObj = id

  -- | Horizontal composition of 2-cells.
  o :: (a :: kk j k) ~> b -> c ~> d -> (a `O` c) ~> (b `O` d)

  -- | Observe constraints from a 2-cell value.
  (\\\) :: ((Ob0 kk i, Ob0 kk j, Ob ps, Ob qs) => r) -> (ps :: kk i j) ~> qs -> r

  leftUnitor :: forall {i} {j} a. (Ob0 kk i, Ob0 kk j, Ob (a :: kk i j)) => (I `O` a) ~> a
  leftUnitorInv :: forall {i} {j} a. (Ob0 kk i, Ob0 kk j, Ob (a :: kk i j)) => a ~> (I `O` a)
  rightUnitor :: forall {i} {j} a. (Ob0 kk i, Ob0 kk j, Ob (a :: kk i j)) => (a `O` I) ~> a
  rightUnitorInv :: forall {i} {j} a. (Ob0 kk i, Ob0 kk j, Ob (a :: kk i j)) => a ~> (a `O` I)
  associator
    :: forall {h} {i} {j} {k} a b c
     . (Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob (a :: kk j k), Ob (b :: kk i j), Ob (c :: kk h i))
    => (a `O` b) `O` c ~> a `O` (b `O` c)
  associatorInv
    :: forall {h} {i} {j} {k} a b c
     . (Ob0 kk h, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob (a :: kk j k), Ob (b :: kk i j), Ob (c :: kk h i))
    => a `O` (b `O` c) ~> (a `O` b) `O` c

leftUnitor' :: (Bicategory kk) => (a :: kk i j) ~> b -> (I `O` a) ~> b
leftUnitor' f = f . leftUnitor \\\ f

leftUnitorInv' :: (Bicategory kk) => (a :: kk i j) ~> b -> a ~> (I `O` b)
leftUnitorInv' f = leftUnitorInv . f \\\ f

rightUnitor' :: (Bicategory kk) => (a :: kk i j) ~> b -> (a `O` I) ~> b
rightUnitor' f = f . rightUnitor \\\ f

rightUnitorInv' :: (Bicategory kk) => (a :: kk i j) ~> b -> a ~> (b `O` I)
rightUnitorInv' f = rightUnitorInv . f \\\ f

associator'
  :: forall kk {i} {j} (a :: kk i j) b c. (Bicategory kk) => Obj a -> Obj b -> Obj c -> (a `O` b) `O` c ~> a `O` (b `O` c)
associator' a b c = associator @kk @a @b @c \\\ a \\\ b \\\ c

associatorInv'
  :: forall kk {i} {j} (a :: kk i j) b c. (Bicategory kk) => Obj a -> Obj b -> Obj c -> a `O` (b `O` c) ~> (a `O` b) `O` c
associatorInv' a b c = associatorInv @kk @a @b @c \\\ a \\\ b \\\ c

leftUnitorWith :: (Bicategory kk) => (c ~> (I :: kk i i)) -> a ~> b -> (c `O` a) ~> b
leftUnitorWith c ab = (leftUnitor . (c `o` ab)) \\\ ab

leftUnitorInvWith :: (Bicategory kk) => ((I :: kk i i) ~> c) -> a ~> b -> a ~> (c `O` b)
leftUnitorInvWith c ab = ((c `o` ab) . leftUnitorInv) \\\ ab

rightUnitorWith :: (Bicategory kk) => (c ~> (I :: kk i i)) -> a ~> b -> (a `O` c) ~> b
rightUnitorWith c ab = (rightUnitor . (ab `o` c)) \\\ ab

rightUnitorInvWith :: (Bicategory kk) => ((I :: kk i i) ~> c) -> a ~> b -> a ~> (b `O` c)
rightUnitorInvWith c ab = ((ab `o` c) . rightUnitorInv) \\\ ab

appendObj
  :: forall {kk} {i} {j} {k} (a :: kk j k) (b :: kk i j) r
   . (Bicategory kk, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob a, Ob b)
  => ((Ob (a `O` b)) => r)
  -> r
appendObj r = r \\\ (obj @a `o` obj @b)

(||) :: (Bicategory kk) => ((a :: kk i j) ~> b) -> (c ~> d) -> O a c ~> O b d
(||) = o

(==) :: (CategoryOf k) => ((a :: k) ~> b) -> (b ~> c) -> a ~> c
f == g = g . f

type Monad :: forall {kk} {a}. kk a a -> Constraint
class (Bicategory kk, Ob0 kk a) => Monad (t :: kk a a) where
  eta :: I ~> t
  mu :: t `O` t ~> t

type Comonad :: forall {kk} {a}. kk a a -> Constraint
class (Bicategory kk, Ob0 kk a) => Comonad (t :: kk a a) where
  epsilon :: t ~> I
  delta :: t ~> t `O` t

type Bimodule :: forall {kk} {a} {b}. kk a a -> kk b b -> kk b a -> Constraint
class (Monad s, Monad t) => Bimodule s t p where
  leftAction :: s `O` p ~> p
  rightAction :: p `O` t ~> p

instance {-# OVERLAPPABLE #-} (Monad s) => Bimodule s s s where
  leftAction = mu
  rightAction = mu

type Adjunction :: forall {kk} {c} {d}. kk c d -> kk d c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d) => Adjunction (l :: kk c d) (r :: kk d c) where
  unit :: I ~> r `O` l
  counit :: l `O` r ~> I

leftAdjunct
  :: forall {kk} {c} {d} {i} (l :: kk c d) (r :: kk d c) (a :: kk i c) b
   . (Adjunction l r, Ob a, Ob r, Ob l, Ob0 kk i)
  => l `O` a ~> b
  -> a ~> r `O` b
leftAdjunct f =
  leftUnitorInv
    == unit @l @r || obj @a
    == associator @_ @r @l @a
    == obj @r || f

rightAdjunct
  :: forall {kk} {c} {d} {i} (l :: kk c d) (r :: kk d c) (a :: kk i c) b
   . (Adjunction l r, Ob b, Ob r, Ob l, Ob0 kk i)
  => a ~> r `O` b
  -> l `O` a ~> b
rightAdjunct f =
  obj @l || f
    == associatorInv @_ @l @r @b
    == counit @l @r || obj @b
    == leftUnitor
