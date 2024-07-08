{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory (
  -- * Bicategories
  Bicategory(..)
  , BicategoryConstraints
  , IIsOb
  , appendObj

  -- * Paths
  , Path(..)
  , SPath(..)
  , IsPath(..)
  , asObj
  , asSPath
  , type (+++)
  , append
  , withAssoc
  , withUnital
  , Strictified(..)
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
  , Monad(..)
  , Comonad(..)
  , Adjunction(..)
  , Bimodule(..)
)
where

import Data.Kind (Constraint, Type)

import Proarrow.Core (CategoryOf(..), CAT, id, Any, Profunctor(..), Promonad(..), dimapDefault)
import Proarrow.Object (Obj, obj)
import Prelude (($), type (~))

infixr 5 :::
infixl 5 +++

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
  SNil :: Ob0 kk k => SPath (Nil :: Path kk k k)
  SCons :: forall {kk} {j} {k} (p :: kk j k) ps. (Ob0 kk j, Ob0 kk k) => Obj p -> SPath ps -> SPath (p ::: ps)

type IsPath :: forall {kk} {j} {k}. Path kk j k -> Constraint
class IsPath (ps :: Path kk j k) where
  singPath :: SPath ps
instance Ob0 kk k => IsPath (Nil :: Path kk k k) where
  singPath = SNil
instance (Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob (p :: kk i j), IsPath (ps :: Path kk j k), Bicategory kk) => IsPath (p ::: ps) where
  singPath = let p = obj @p in SCons p singPath

append :: SPath ps -> SPath qs -> SPath (ps +++ qs)
append SNil qs = qs
append (SCons p ps) qs = SCons p (append ps qs)

singleton :: (Bicategory kk, Ob0 kk i, Ob0 kk j) => (p :: kk i j) ~> q -> (p ::: Nil) ~> (q ::: Nil)
singleton f = Str f \\ f

obj1 :: forall {kk} {i} {j} p. (Bicategory kk, Ob (p :: kk i j), Ob0 kk i, Ob0 kk j) => Obj (p ::: Nil)
obj1 = singleton (obj @p)

asObj :: Bicategory kk => SPath (ps :: Path kk i j) -> Obj ps
asObj SNil = obj
asObj (SCons p SNil) = singleton p
asObj (SCons p ps@SCons{}) = singleton p `o` asObj ps \\ p

asSPath :: Bicategory kk => Obj (ps :: Path kk i j) -> SPath ps
asSPath p = singPath \\\ p

withAssoc
  :: forall {kk} {h} {i} {j} {k} (a :: Path kk h i) (b :: Path kk i j) (c :: Path kk j k) r
   . Bicategory kk
  => Obj a -> Obj b -> Obj c -> (((a +++ b) +++ c ~ a +++ (b +++ c)) => r) -> r
withAssoc as@Str{} Str{} Str{} = go (asSPath as)
  where
    go :: forall a'. SPath a' -> (((a' +++ b) +++ c ~ a' +++ (b +++ c)) => r) -> r
    go SNil r = r
    go (SCons _ a) r = go a r

withUnital
  :: forall {kk} {j} {k} (a :: Path kk j k) r
   . Bicategory kk
  => Obj a -> (a +++ Nil ~ a => r) -> r
withUnital Str{} = go (singPath @a)
  where
    go :: forall a'. SPath a' -> (a' +++ Nil ~ a' => r) -> r
    go SNil r = r
    go (SCons _ a) r = go a r

concatFold
  :: forall {kk} {i} {j} {k} (as :: Path kk i j) (bs :: Path kk j k). (Ob as, Ob bs, Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk)
  => Fold as `O` Fold bs ~> Fold (as +++ bs)
concatFold =
  let fbs = fold (singPath @bs)
      h :: forall cs. SPath cs -> (Fold cs `O` Fold bs) ~> Fold (cs +++ bs)
      h SNil = leftUnitor fbs
      -- h (SCons c cs) = (c `o` h cs) . associator c (fold cs) fbs
      h (SCons c SNil) = case singPath @bs of
        SNil -> rightUnitor c
        SCons{} -> c `o` fbs
      h (SCons c cs@SCons{}) = (c `o` h cs) . associator c (fold cs) fbs
  in h (singPath @as)

splitFold
  :: forall {kk} {i} {j} {k} (as :: Path kk i j) (bs :: Path kk j k). (Ob as, Ob bs, Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk)
  => Fold (as +++ bs) ~> Fold as `O` Fold bs
splitFold =
  let fbs = fold (singPath @bs)
      h :: forall cs. SPath cs -> Fold (cs +++ bs) ~> Fold cs `O` Fold bs
      h SNil = leftUnitorInv fbs
      -- h (SCons c cs) = associatorInv c (fold cs) fbs . (c `o` h cs)
      h (SCons c SNil) = case singPath @bs of
        SNil -> rightUnitorInv c
        SCons{} -> c `o` fbs
      h (SCons c cs@SCons{}) = associatorInv c (fold cs) fbs . (c `o` h cs)
  in h (singPath @as)

type family Fold (as :: Path kk j k) :: kk j k
type instance Fold (Nil :: Path kk j j) = (I :: kk j j)
-- type instance Fold (p ::: ps) = p `O` Fold ps
type instance Fold (p ::: Nil) = p
type instance Fold (p ::: (q ::: ps)) = p `O` Fold (q ::: ps)

fold :: forall {kk} {i} {j} (as :: Path kk i j). Bicategory kk => SPath as -> Fold as ~> Fold as
fold SNil = id
-- fold (SCons p ps) = p `o` fold ps
fold (SCons p SNil) = p
fold (SCons p fs@SCons{}) = p `o` fold fs


type Strictified :: CAT (Path kk j k)
data Strictified ps qs where
  Str :: forall {kk} {j} {k} (ps :: Path kk j k) qs. (Ob ps, Ob qs, Ob0 kk j, Ob0 kk k) => Fold ps ~> Fold qs -> Strictified ps qs

mkStr :: forall {kk} {j} {k} (ps :: Path kk j k) qs. (Bicategory kk, IsPath ps, IsPath qs, Ob0 kk j, Ob0 kk k) => (Fold ps ~> Fold qs) -> Strictified ps qs
mkStr f = Str f \\ f

instance (CategoryOf (kk j k), Ob0 kk j, Ob0 kk k, Bicategory kk) => Profunctor (Strictified :: CAT (Path kk j k)) where
  dimap = dimapDefault
  r \\ Str{} = r
instance (CategoryOf (kk j k), Ob0 kk j, Ob0 kk k, Bicategory kk) => Promonad (Strictified :: CAT (Path kk j k)) where
  id :: forall (a :: Path kk j k). Ob a => Strictified a a
  id = Str (fold (singPath @a))
  Str m . Str n = Str (m . n)
instance (CategoryOf (kk j k), Ob0 kk j, Ob0 kk k, Bicategory kk) => CategoryOf (Path kk j k) where
  type (~>) = Strictified
  type Ob (ps :: Path kk j k) = (IsPath ps, Ob (Fold ps))

introI :: forall {kk} {j}. (Ob0 kk j, Bicategory kk) => (Nil :: Path kk j j) ~> (I ::: Nil)
introI = Str obj

elimI :: forall {kk} {j}. (Ob0 kk j, Bicategory kk) => (I ::: Nil) ~> (Nil :: Path kk j j)
elimI = Str obj

introO
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k). (Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk, Ob p, Ob q)
  => (p ::: q ::: Nil) ~> (p `O` q ::: Nil)
introO = Str id \\ (obj @p `o` obj @q)

elimO
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k). (Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk, Ob p, Ob q)
  => (p `O` q ::: Nil) ~> (p ::: q ::: Nil)
elimO = Str id \\ (obj @p `o` obj @q)


class Ob (I :: kk i i) => IIsOb kk i
instance Ob (I :: kk i i) => IIsOb kk i

class (forall j k. (Ob0 kk j, Ob0 kk k) => CategoryOf (kk j k), forall i. Ob0 kk i => IIsOb kk i) => BicategoryConstraints kk
instance (forall j k. (Ob0 kk j, Ob0 kk k) => CategoryOf (kk j k), forall i. Ob0 kk i => IIsOb kk i) => BicategoryConstraints kk

-- | Bicategories.
--
-- * 0-cells are kinds @i@, @j@, @k@... satisfying the @Ob0 kk@ constraint.
-- * 1-cells are types of kind @kk j k@ for any 0-cells @j@ and @k@, satisfying the @Ob@ constraint.
-- * 2-cells are values of type @p ~> q@, where @p@ and @q@ are 1-cells.
type Bicategory :: CAT k -> Constraint
class BicategoryConstraints kk => Bicategory kk where
  type Ob0 kk (j :: k) :: Constraint
  type Ob0 kk j = Any j
  type I :: kk i i
  type O (p :: kk i j) (q :: kk j k) :: kk i k
  -- | Horizontal composition of 2-cells.
  o :: (a :: kk i j) ~> b -> c ~> d -> (a `O` c) ~> (b `O` d)
  -- | Observe constraints from a 2-cell value.
  (\\\) :: ((Ob0 kk i, Ob0 kk j, Ob ps, Ob qs) => r) -> (ps :: kk i j) ~> qs -> r
  leftUnitor :: Obj (a :: kk i j) -> (I `O` a) ~> a
  leftUnitorInv :: Obj (a :: kk i j) -> a ~> (I `O` a)
  rightUnitor :: Obj (a :: kk i j) -> (a `O` I) ~> a
  rightUnitorInv :: Obj (a :: kk i j) -> a ~> (a `O` I)
  associator :: Obj (a :: kk i j) -> Obj b -> Obj c -> (a `O` b) `O` c ~> a `O` (b `O` c)
  associatorInv :: Obj (a :: kk i j) -> Obj b -> Obj c -> a `O` (b `O` c) ~> (a `O` b) `O` c

appendObj
  :: forall {kk} {i} {j} {k} (a :: kk i j) (b :: kk j k) r
   . (Bicategory kk, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob a, Ob b)
  => (Ob (a `O` b) => r) -> r
appendObj r = r \\\ (obj @a `o` obj @b)


instance Bicategory kk => Bicategory (Path kk) where
  type Ob0 (Path kk) j = Ob0 kk j
  type I = Nil
  type O ps qs = ps +++ qs
  r \\\ Str{} = r
  Str @as @bs ps `o` Str @cs @ds qs =
    appendObj @as @cs $ appendObj @bs @ds $
      Str (concatFold @bs @ds . (ps `o` qs) . splitFold @as @cs)
  leftUnitor p = p
  leftUnitorInv p = p
  rightUnitor p = withUnital p p
  rightUnitorInv p = withUnital p p
  associator p@Str{} q@Str{} r@Str{} = withAssoc p q r (p `o` (q `o` r))
  associatorInv p@Str{} q@Str{} r@Str{} = withAssoc p q r (p `o` (q `o` r))



type Monad :: forall {kk} {a}. kk a a -> Constraint
class (Bicategory kk, Ob0 kk a, Ob t) => Monad (t :: kk a a) where
  eta :: I ~> t
  mu :: t `O` t ~> t

instance (Bicategory (Path kk), Ob0 kk a) => Monad (Nil :: Path kk a a) where
  eta = id
  mu = id

class (Bicategory kk, Ob0 kk a, Ob t) => Comonad (t :: kk a a) where
  epsilon :: t ~> I
  delta :: t ~> t `O` t

instance (Bicategory (Path kk), Ob0 kk a) => Comonad (Nil :: Path kk a a) where
  epsilon = id
  delta = id

class (Monad s, Monad t) => Bimodule s t (p :: kk a b) where
  leftAction :: s `O` p ~> p
  rightAction :: p `O` t ~> p

instance {-# OVERLAPPABLE #-} Monad s => Bimodule s s s where
  leftAction = mu
  rightAction = mu

type Adjunction :: forall {kk} {c} {d}. kk c d -> kk d c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob l, Ob r) => Adjunction (l :: kk c d) (r :: kk d c) where
  unit :: I ~> r `O` l
  counit :: l `O` r ~> I

instance (Adjunction l r, Ob (r `O` l)) => Monad (r ::: l ::: Nil) where
  eta = Str (unit @l @r)
  mu = let r = obj @r; l = obj @l in mkStr (r `o` (leftUnitor l . (counit @l @r `o` l) . associatorInv l r l))

instance (Adjunction l r, Ob (l `O` r)) => Comonad (l ::: r ::: Nil) where
  epsilon = Str (counit @l @r)
  delta = let r = obj @r; l = obj @l in mkStr (l `o` (associator r l r . (unit @l @r `o` r) . leftUnitorInv r))