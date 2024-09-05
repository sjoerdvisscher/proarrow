{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Category.Bicategory
  ( -- * Bicategories
    Bicategory (..)
  , (==)
  , (||)
  , appendObj
  , leftUnitorWith
  , leftUnitorInvWith
  , rightUnitorWith
  , rightUnitorInvWith

    -- * Paths
  , Path (..)
  , SPath (..)
  , IsPath (..)
  , withIsPath
  , asObj
  , asSPath
  , type (+++)
  , append
  , singleton
  , withAssoc
  , withUnital
  , Strictified (..)
  , str
  , unStr
  , Fold
  , fold
  , obj1
  , concatFold
  , splitFold
  , introI
  , elimI
  , introO
  , elimO

    -- * More
  , Monad (..)
  , Comonad (..)
  , Adjunction (..)
  , Bimodule (..)
  )
where

import Data.Kind (Constraint, Type)

import Proarrow.Core (Any, CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, id, src, tgt)
import Proarrow.Object (Obj, obj)
import Prelude (($), type (~))

infixr 5 :::
infixl 5 +++
infixl 8 ||
infixl 7 ==

-- | The type of 2-parameter kind constructors.
type Path :: CAT k -> CAT k

-- | A type-level kind-threaded list. Used to strictify the bicategory and double category definitions.
-- @kk@ is a kind constructor, which creates a kind given two other kinds. (Each kind representing a 0-cell.)
type data Path kk j k where
  Nil :: Path kk k k
  (:::) :: kk i j -> Path kk j k -> Path kk i k

type family (+++) (ps :: Path kk a b) (qs :: Path kk b c) :: Path kk a c
type instance Nil +++ qs = qs
type instance (p ::: ps) +++ qs = p ::: (ps +++ qs)

type SPath :: Path kk j k -> Type
data SPath ps where
  SNil :: (Ob0 kk k) => SPath (Nil :: Path kk k k)
  SCons :: forall {kk} {i} {j} {k} (p :: kk i j) (ps :: Path kk j k). (Ob0 kk i) => Obj p -> SPath ps -> SPath (p ::: ps)

type IsPath :: forall {kk} {j} {k}. Path kk j k -> Constraint
class (Bicategory kk, Ob0 kk j, Ob0 kk k) => IsPath (ps :: Path kk j k) where
  singPath :: SPath ps
instance (Bicategory kk, Ob0 kk k) => IsPath (Nil :: Path kk k k) where
  singPath = SNil
instance (Ob0 kk i, Ob (p :: kk i j), IsPath (ps :: Path kk j k)) => IsPath (p ::: ps) where
  singPath = let p = obj @p in SCons p singPath

withIsPath :: (Bicategory kk) => SPath (ps :: Path kk j k) -> ((IsPath ps, Ob0 kk j, Ob0 kk k) => r) -> r
withIsPath SNil r = r
withIsPath (SCons p ps) r = withIsPath ps r \\\ p

append :: SPath ps -> SPath qs -> SPath (ps +++ qs)
append SNil qs = qs
append (SCons p ps) qs = SCons p (append ps qs)

singleton :: (Bicategory kk) => (p :: kk i j) ~> q -> (p ::: Nil) ~> (q ::: Nil)
singleton f = Str (SCons (src f) SNil) (SCons (tgt f) SNil) f \\\ f

obj1 :: forall {kk} {i} {j} p. (Bicategory kk, Ob (p :: kk i j), Ob0 kk i, Ob0 kk j) => Obj (p ::: Nil)
obj1 = singleton (obj @p)

asObj :: (Bicategory kk) => SPath (ps :: Path kk i j) -> Obj ps
asObj SNil = obj
asObj (SCons p SNil) = singleton p
asObj (SCons p ps@SCons{}) = asObj ps `o` singleton p \\ p

asSPath :: (Bicategory kk) => Obj (ps :: Path kk i j) -> SPath ps
asSPath (Str p _ _) = p

withAssoc
  :: forall {kk} {h} {i} {j} {k} (a :: Path kk h i) (b :: Path kk i j) (c :: Path kk j k) r
   . (Bicategory kk)
  => Obj a
  -> Obj b
  -> Obj c
  -> (((a +++ b) +++ c ~ a +++ (b +++ c)) => r)
  -> r
withAssoc as@Str{} Str{} Str{} = go (asSPath as)
  where
    go :: forall a'. SPath a' -> (((a' +++ b) +++ c ~ a' +++ (b +++ c)) => r) -> r
    go SNil r = r
    go (SCons _ a) r = go a r

withUnital
  :: forall {kk} {j} {k} (a :: Path kk j k) r
   . (Bicategory kk)
  => SPath a
  -> ((a +++ Nil ~ a) => r)
  -> r
withUnital = go
  where
    go :: forall a'. SPath a' -> ((a' +++ Nil ~ a') => r) -> r
    go SNil r = r
    go (SCons _ a) r = go a r

concatFold
  :: forall {kk} {i} {j} {k} (as :: Path kk i j) (bs :: Path kk j k)
   . (Bicategory kk)
  => SPath as
  -> SPath bs
  -> Fold bs `O` Fold as ~> Fold (as +++ bs)
concatFold as bs =
  let fbs = fold bs
      h :: forall cs. (Ob0 kk k) => SPath cs -> (Fold bs `O` Fold cs) ~> Fold (cs +++ bs)
      h SNil = rightUnitor fbs
      h (SCons c SNil) = case bs of
        SNil -> leftUnitor c
        SCons{} -> fbs `o` c
      h (SCons c cs@SCons{}) = (h cs `o` c) . associatorInv fbs (fold cs) c
  in h as \\\ fbs

splitFold
  :: forall {kk} {i} {j} {k} (as :: Path kk i j) (bs :: Path kk j k)
   . (Bicategory kk)
  => SPath as
  -> SPath bs
  -> Fold (as +++ bs) ~> Fold bs `O` Fold as
splitFold as bs =
  let fbs = fold bs
      h :: forall cs. (Ob0 kk k) => SPath cs -> Fold (cs +++ bs) ~> Fold bs `O` Fold cs
      h SNil = rightUnitorInv fbs
      h (SCons c SNil) = case bs of
        SNil -> leftUnitorInv c
        SCons{} -> fbs `o` c
      h (SCons c cs@SCons{}) = associator fbs (fold cs) c . (h cs `o` c)
  in h as \\\ fbs

type family Fold (as :: Path kk j k) :: kk j k
type instance Fold (Nil :: Path kk j j) = (I :: kk j j)
type instance Fold (p ::: Nil) = p
type instance Fold (p ::: (q ::: ps)) = Fold (q ::: ps) `O` p

fold :: forall {kk} {i} {j} (as :: Path kk i j). (Bicategory kk) => SPath as -> Fold as ~> Fold as
fold SNil = iObj
fold (SCons p SNil) = p
fold (SCons p fs@SCons{}) = fold fs `o` p

type Strictified :: CAT (Path kk j k)
data Strictified ps qs where
  Str
    :: forall {kk} {j} {k} (ps :: Path kk j k) qs
     . (Ob0 kk j, Ob0 kk k)
    => SPath ps
    -> SPath qs
    -> Fold ps ~> Fold qs
    -> Strictified ps qs

str :: (Bicategory kk) => Obj (ps :: Path kk j k) -> Obj qs -> (Fold ps ~> Fold qs) -> Strictified ps qs
str ps qs f = Str (asSPath ps) (asSPath qs) f \\\ f

unStr :: Strictified ps qs -> Fold ps ~> Fold qs
unStr (Str _ _ f) = f

instance (CategoryOf (kk j k), Bicategory kk) => Profunctor (Strictified :: CAT (Path kk j k)) where
  dimap = dimapDefault
  r \\ Str ps qs _ = withIsPath ps (withIsPath qs r)
instance (CategoryOf (kk j k), Bicategory kk) => Promonad (Strictified :: CAT (Path kk j k)) where
  id :: forall (a :: Path kk j k). (Ob a) => Strictified a a
  id = let a = singPath @a in Str a a (fold a)
  Str _ r m . Str p _ n = Str p r (m . n)
instance (CategoryOf (kk j k), Bicategory kk) => CategoryOf (Path kk j k) where
  type (~>) = Strictified
  type Ob (ps :: Path kk j k) = (IsPath ps, Ob0 kk j, Ob0 kk k)

introI :: forall {kk} {j}. (Ob0 kk j, Bicategory kk) => (Nil :: Path kk j j) ~> (I ::: Nil)
introI = Str SNil (SCons iObj SNil) iObj

elimI :: forall {kk} {j}. (Ob0 kk j, Bicategory kk) => (I ::: Nil) ~> (Nil :: Path kk j j)
elimI = Str (SCons iObj SNil) SNil iObj

introO
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k)
   . (Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk, Ob p, Ob q)
  => (p ::: q ::: Nil) ~> (q `O` p ::: Nil)
introO = let p = obj @p; q = obj @q; pq = q `o` p in Str (SCons p (SCons q SNil)) (SCons pq SNil) pq

elimO
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k)
   . (Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk, Ob p, Ob q)
  => (q `O` p ::: Nil) ~> (p ::: q ::: Nil)
elimO = let p = obj @p; q = obj @q; pq = q `o` p in Str (SCons pq SNil) (SCons p (SCons q SNil)) pq

-- | A bicategory is locally "something" if each hom-category is "something".
class (forall j k. (Ob0 kk j, Ob0 kk k) => c (kk j k)) => Locally c kk
instance (forall j k. (Ob0 kk j, Ob0 kk k) => c (kk j k)) => Locally c kk

-- | Bicategories.
--
-- * 0-cells are kinds @i@, @j@, @k@... satisfying the @Ob0 kk@ constraint.
-- * 1-cells are types of kind @kk j k@ for any 0-cells @j@ and @k@, satisfying the @Ob@ constraint.
-- * 2-cells are values of type @p ~> q@, where @p@ and @q@ are 1-cells.
type Bicategory :: forall {s}. CAT s -> Constraint
class (Locally CategoryOf kk, CategoryOf s) => Bicategory (kk :: CAT s) where
  type Ob0 kk (j :: k) :: Constraint
  type Ob0 kk j = Any j
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

  leftUnitor :: (a :: kk i j) ~> b -> (I `O` a) ~> b
  leftUnitorInv :: (a :: kk i j) ~> b -> a ~> (I `O` b)
  rightUnitor :: (a :: kk i j) ~> b -> (a `O` I) ~> b
  rightUnitorInv :: (a :: kk i j) ~> b -> a ~> (b `O` I)
  associator :: Obj (a :: kk i j) -> Obj b -> Obj c -> (a `O` b) `O` c ~> a `O` (b `O` c)
  associatorInv :: Obj (a :: kk i j) -> Obj b -> Obj c -> a `O` (b `O` c) ~> (a `O` b) `O` c

leftUnitorWith :: (Bicategory kk) => (c ~> (I :: kk i i)) -> a ~> b -> (c `O` a) ~> b
leftUnitorWith c ab = (leftUnitor ab . (c `o` src ab)) \\\ ab

leftUnitorInvWith :: (Bicategory kk) => ((I :: kk i i) ~> c) -> a ~> b -> a ~> (c `O` b)
leftUnitorInvWith c ab = ((c `o` tgt ab) . leftUnitorInv ab) \\\ ab

rightUnitorWith :: (Bicategory kk) => (c ~> (I :: kk i i)) -> a ~> b -> (a `O` c) ~> b
rightUnitorWith c ab = (rightUnitor ab . (src ab `o` c)) \\\ ab

rightUnitorInvWith :: (Bicategory kk) => ((I :: kk i i) ~> c) -> a ~> b -> a ~> (b `O` c)
rightUnitorInvWith c ab = ((tgt ab `o` c) . rightUnitorInv ab) \\\ ab

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

instance (Bicategory kk) => Bicategory (Path kk) where
  type Ob0 (Path kk) j = Ob0 kk j
  type I = Nil
  type O ps qs = qs +++ ps
  r \\\ Str ps qs _ = withIsPath ps $ withIsPath qs r
  Str cs ds qs `o` Str as bs ps = Str (append as cs) (append bs ds) (concatFold bs ds . (qs `o` ps) . splitFold as cs)
  leftUnitor f@(Str ps _ _) = withUnital ps f
  leftUnitorInv f@(Str _ ps _) = withUnital ps f
  rightUnitor p = p
  rightUnitorInv p = p
  associator p@Str{} q@Str{} r@Str{} = withAssoc r q p (p `o` (q `o` r))
  associatorInv p@Str{} q@Str{} r@Str{} = withAssoc r q p (p `o` (q `o` r))

type Monad :: forall {kk} {a}. kk a a -> Constraint
class (Bicategory kk, Ob0 kk a, Ob t) => Monad (t :: kk a a) where
  eta :: I ~> t
  mu :: t `O` t ~> t

instance (Bicategory kk, Ob0 kk a) => Monad (Nil :: Path kk a a) where
  eta = iObj
  mu = iObj

instance (Monad s) => Monad (s ::: Nil) where
  eta = str iObj (obj1 @s) eta
  mu = str (obj1 @s || obj1 @s) (obj1 @s) mu

type Comonad :: forall {kk} {a}. kk a a -> Constraint
class (Bicategory kk, Ob0 kk a, Ob t) => Comonad (t :: kk a a) where
  epsilon :: t ~> I
  delta :: t ~> t `O` t

instance (Bicategory kk, Ob0 kk a) => Comonad (Nil :: Path kk a a) where
  epsilon = iObj
  delta = iObj

type Bimodule :: forall {kk} {a} {b}. kk a a -> kk b b -> kk b a -> Constraint
class (Monad s, Monad t, Ob p) => Bimodule s t p where
  leftAction :: s `O` p ~> p
  rightAction :: p `O` t ~> p

-- instance {-# OVERLAPPABLE #-} (Monad s) => Bimodule s s s where
--   leftAction = mu
--   rightAction = mu

type Adjunction :: forall {kk} {c} {d}. kk c d -> kk d c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob l, Ob r) => Adjunction (l :: kk c d) (r :: kk d c) where
  unit :: I ~> r `O` l
  counit :: l `O` r ~> I

instance (Adjunction l r) => Monad (l ::: r ::: Nil) where
  eta = str iObj (obj1 @r || obj1 @l) (unit @l @r)
  mu = let r = obj1 @r; l = obj1 @l in r || str (l || r) iObj (counit @l @r) || l

instance (Adjunction l r) => Comonad (r ::: l ::: Nil) where
  epsilon = str (obj1 @l || obj1 @r) iObj (counit @l @r)
  delta = let r = obj1 @r; l = obj1 @l in l || str iObj (r || l) (unit @l @r) || r
