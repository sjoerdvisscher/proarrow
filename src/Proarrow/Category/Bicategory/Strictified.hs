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
import Proarrow.Category.Bicategory.Sub (IsOb, SUBCAT, WithObO2 (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, id)
import Proarrow.Object (Obj, obj)
import Prelude (type (~))

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
  withIsPath2 :: (IsPath qs) => ((Ob (ps +++ qs)) => r) -> r
  withPathO2 :: (IsOb tag ps, IsOb tag qs, Ob qs) => ((IsOb tag (ps +++ qs), Ob (ps +++ qs)) => r) -> r
instance (Bicategory kk, Ob0 kk k) => IsPath (Nil :: Path kk k k) where
  singPath = SNil
  withIsPath2 r = r
  withPathO2 r = r
instance (Ob0 kk i, Ob (p :: kk i j), IsPath (ps :: Path kk j k)) => IsPath (p ::: ps) where
  singPath = let p = obj @p in SCons p singPath
  withIsPath2 @qs r = withIsPath2 @ps @qs r
  withPathO2 @tag @qs r = withPathO2 @ps @tag @qs r

withIsPath :: (Bicategory kk) => SPath (ps :: Path kk j k) -> ((Ob ps, Ob0 kk j, Ob0 kk k) => r) -> r
withIsPath SNil r = r
withIsPath (SCons p ps) r = withIsPath ps r \\\ p

append :: SPath ps -> SPath qs -> SPath (ps +++ qs)
append SNil qs = qs
append (SCons p ps) qs = SCons p (append ps qs)

singleton :: (Bicategory kk) => (p :: kk i j) ~> q -> (p ::: Nil) ~> (q ::: Nil)
singleton f = St f \\\ f

obj1 :: forall {kk} {i} {j} p. (Bicategory kk, Ob (p :: kk i j), Ob0 kk i, Ob0 kk j) => Obj (p ::: Nil)
obj1 = singleton (obj @p)

asObj :: (Bicategory kk) => SPath (ps :: Path kk i j) -> Obj ps
asObj SNil = obj
asObj (SCons p SNil) = singleton p
asObj (SCons p ps@SCons{}) = asObj ps `o` singleton p \\ p

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
fold SNil = id
fold (SCons p SNil) = p
fold (SCons p fs@SCons{}) = fold fs `o` p

combineAll :: forall {kk} {i} {j} (as :: Path kk i j). (Bicategory kk, Ob as) => as ~> (Fold as ::: Nil)
combineAll = let n = fold (singPath @as) in St n \\ n

splitAll :: forall {kk} {i} {j} (as :: Path kk i j). (Bicategory kk, Ob as) => (Fold as ::: Nil) ~> as
splitAll = let n = fold (singPath @as) in St n \\ n

type Strictified :: CAT (Path kk j k)
data Strictified ps qs where
  St
    :: forall {kk} {j} {k} (ps :: Path kk j k) qs
     . (Ob ps, Ob qs)
    => Fold ps ~> Fold qs
    -> Strictified ps qs

view :: Strictified (ps :: Path kk j k) qs -> (Strictified ps qs, SPath ps, SPath qs)
view (St f) = (St f, singPath, singPath)

pattern Str
  :: forall {kk} {j} {k} (ps :: Path kk j k) (qs :: Path kk j k)
   . (Bicategory kk)
  => (Ob0 kk j, Ob0 kk k)
  => SPath ps
  -> SPath qs
  -> (Fold ps ~> Fold qs)
  -> Strictified ps qs
pattern Str ps qs f <- (view -> (St f, ps, qs))
  where
    Str ps qs f = withIsPath ps (withIsPath qs (St @ps @qs f))

{-# COMPLETE Str #-}

unStr :: Strictified ps qs -> Fold ps ~> Fold qs
unStr (St f) = f

instance (CategoryOf (kk j k), Bicategory kk) => Profunctor (Strictified :: CAT (Path kk j k)) where
  dimap = dimapDefault
  r \\ St _ = r
instance (CategoryOf (kk j k), Bicategory kk) => Promonad (Strictified :: CAT (Path kk j k)) where
  id :: forall (as :: Path kk j k). (Ob as) => Strictified as as
  id = St @as @as (fold (singPath @as))
  St m . St n = St (m . n)
instance (CategoryOf (kk j k), Bicategory kk) => CategoryOf (Path kk j k) where
  type (~>) = Strictified
  type Ob (ps :: Path kk j k) = (IsPath ps, Ob0 kk j, Ob0 kk k)

introI :: forall {kk} {j}. (Ob0 kk j, Bicategory kk) => (Nil :: Path kk j j) ~> (I ::: Nil)
introI = St id

elimI :: forall {kk} {j}. (Ob0 kk j, Bicategory kk) => (I ::: Nil) ~> (Nil :: Path kk j j)
elimI = St id

introO
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k)
   . (Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk, Ob p, Ob q)
  => (p ::: q ::: Nil) ~> (q `O` p ::: Nil)
introO = let p = obj @p; q = obj @q; pq = q `o` p in St pq \\ pq

elimO
  :: forall {kk} {i} {j} {k} (p :: kk i j) (q :: kk j k)
   . (Ob0 kk i, Ob0 kk j, Ob0 kk k, Bicategory kk, Ob p, Ob q)
  => (q `O` p ::: Nil) ~> (p ::: q ::: Nil)
elimO = let p = obj @p; q = obj @q; pq = q `o` p in St pq \\ pq

instance (Bicategory kk) => Bicategory (Path kk) where
  type Ob0 (Path kk) j = Ob0 kk j
  type I = Nil
  type O ps qs = qs +++ ps
  withOb2 @ps @qs = withIsPath2 @qs @ps
  withOb0s @ps r = case singPath @ps of
    SNil -> r
    SCons @p p ps -> withOb0s @kk @p (withIsPath ps r) \\\ p
  r \\\ St _ = r
  Str cs ds qs `o` Str as bs ps = Str (append as cs) (append bs ds) (concatFold bs ds . (qs `o` ps) . splitFold as cs)
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @p @q @r = obj @p `o` obj @q `o` obj @r
  associatorInv @p @q @r = obj @p `o` obj @q `o` obj @r

stUnit :: forall {kk} {i} {j} (p :: kk i j) q. (Adjunction p q, Ob p, Ob q) => Nil ~> p ::: q ::: Nil
stUnit = withOb0s @kk @p (St (unit @p @q))

stCounit :: forall {kk} {i} {j} (p :: kk i j) q. (Adjunction p q, Ob p, Ob q) => q ::: p ::: Nil ~> Nil
stCounit = withOb0s @kk @p (St (counit @p @q))

instance (Bicategory kk, Ob0 kk a) => Adjunction (Nil :: Path kk a a) Nil where
  unit = id
  counit = id

instance (Bicategory kk, Adjunction (l :: kk j k) r, Ob0 kk j, Ob0 kk k) => Adjunction (l ::: Nil) (r ::: Nil) where
  unit = St (unit @l @r)
  counit = St (counit @l @r)

instance (Bicategory kk, Ob0 kk a) => Monad (Nil :: Path kk a a) where
  eta = id
  mu = id

instance (Monad s, Ob (s :: kk a a), Ob0 kk a) => Monad (s ::: Nil) where
  eta = St @Nil @(s ::: Nil) eta
  mu = St @(s ::: s ::: Nil) @(s ::: Nil) mu

instance (Bicategory kk, Ob0 kk a) => Comonad (Nil :: Path kk a a) where
  epsilon = id
  delta = id

instance (Adjunction l r, Ob (r :: kk i j), Ob l, Ob0 kk i, Ob0 kk j) => Monad (l ::: r ::: Nil) where
  eta = St @Nil @(l ::: r ::: Nil) (unit @l @r)
  mu = obj1 @r || St @(r ::: l ::: Nil) @Nil (counit @l @r) || obj1 @l

instance (Adjunction l r, Ob (r :: kk i j), Ob l, Ob0 kk i, Ob0 kk j) => Comonad (r ::: l ::: Nil) where
  epsilon = St @(r ::: l ::: Nil) @Nil (counit @l @r)
  delta = obj1 @l || St @Nil @(l ::: r ::: Nil) (unit @l @r) || obj1 @r

type instance IsOb tag Nil = ()
type instance IsOb tag (p ::: ps) = (IsOb tag p, IsOb tag ps)
instance (WithObO2 tag kk) => WithObO2 tag (Path kk) where
  withObO2 @a @b r = withPathO2 @b @tag @a r

withIsObTagFold
  :: forall {kk} {j} {k} tag (ps :: Path kk j k) r
   . (Bicategory (SUBCAT tag kk), WithObO2 tag kk, IsOb tag ps, Ob ps) => ((IsOb tag (Fold ps), Ob (Fold ps)) => r) -> r
withIsObTagFold r = case singPath @ps of
  SNil -> r
  SCons c SNil -> r \\ c
  SCons @p @ps' c cs@SCons{} -> withIsObTagFold @tag @ps' (withObO2 @tag @kk @(Fold ps') @p r) \\\ asObj cs \\ c
