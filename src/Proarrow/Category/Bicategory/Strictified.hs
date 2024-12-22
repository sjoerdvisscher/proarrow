{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Strictified where

import Data.Kind (Constraint, Type)

import Proarrow.Category.Bicategory
  ( Adjunction (..)
  , Bicategory (..)
  , Comonad (..)
  , Monad (..)
  , associator'
  , associatorInv'
  , (||)
  )
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, id, src, tgt)
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
  SNil :: (Ob0 kk k) => SPath (Nil :: Path kk k k)
  SCons :: forall {kk} {i} {j} {k} (p :: kk i j) (ps :: Path kk j k). (Ob0 kk i) => Obj p -> SPath ps -> SPath (p ::: ps)

class ((as +++ bs) +++ cs ~ as +++ (bs +++ cs)) => Assoc as bs cs
instance (as +++ (bs +++ cs) ~ (as +++ bs) +++ cs) => Assoc as bs cs

type IsPath :: forall {kk} {j} {k}. Path kk j k -> Constraint
class
  (Bicategory kk, Ob0 kk j, Ob0 kk k, ps +++ Nil ~ ps, forall i h (qs :: Path kk k h) (rs :: Path kk h i). Assoc ps qs rs) =>
  IsPath (ps :: Path kk j k)
  where
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

concatFold
  :: forall {kk} {i} {j} {k} (as :: Path kk i j) (bs :: Path kk j k)
   . (Bicategory kk)
  => SPath as
  -> SPath bs
  -> Fold bs `O` Fold as ~> Fold (as +++ bs)
concatFold as bs =
  let fbs = fold bs
      h :: forall cs. (Ob0 kk k) => SPath cs -> (Fold bs `O` Fold cs) ~> Fold (cs +++ bs)
      h SNil = rightUnitor \\\ fbs
      h (SCons c SNil) = case bs of
        SNil -> leftUnitor \\\ c
        SCons{} -> fbs `o` c
      h (SCons c cs@SCons{}) = (h cs `o` c) . associatorInv' fbs (fold cs) c
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
      h SNil = rightUnitorInv \\\ fbs
      h (SCons c SNil) = case bs of
        SNil -> leftUnitorInv \\\ c
        SCons{} -> fbs `o` c
      h (SCons c cs@SCons{}) = associator' fbs (fold cs) c . (h cs `o` c)
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

instance (Bicategory kk) => Bicategory (Path kk) where
  type Ob0 (Path kk) j = Ob0 kk j
  type I = Nil
  type O ps qs = qs +++ ps
  r \\\ Str ps qs _ = withIsPath ps $ withIsPath qs r
  Str cs ds qs `o` Str as bs ps = Str (append as cs) (append bs ds) (concatFold bs ds . (qs `o` ps) . splitFold as cs)
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @p @q @r = obj @p `o` obj @q `o` obj @r
  associatorInv @p @q @r = obj @p `o` obj @q `o` obj @r

instance (Bicategory kk, Ob0 kk a) => Monad (Nil :: Path kk a a) where
  eta = iObj
  mu = iObj

instance (Monad s, Ob s) => Monad (s ::: Nil) where
  eta = str iObj (obj1 @s) eta
  mu = str (obj1 @s || obj1 @s) (obj1 @s) mu

instance (Bicategory kk, Ob0 kk a) => Comonad (Nil :: Path kk a a) where
  epsilon = iObj
  delta = iObj

instance (Adjunction l r, Ob r, Ob l) => Monad (l ::: r ::: Nil) where
  eta = str iObj (obj1 @r || obj1 @l) (unit @l @r)
  mu = let r = obj1 @r; l = obj1 @l in r || str (l || r) iObj (counit @l @r) || l

instance (Adjunction l r, Ob r, Ob l) => Comonad (r ::: l ::: Nil) where
  epsilon = str (obj1 @l || obj1 @r) iObj (counit @l @r)
  delta = let r = obj1 @r; l = obj1 @l in l || str iObj (r || l) (unit @l @r) || r
