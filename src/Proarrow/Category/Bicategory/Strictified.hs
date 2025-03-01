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
  , iObj
  , leftUnitorInvWith
  , leftUnitorWith
  , rightUnitorWith
  , (==)
  , (||)
  )
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), RetroSq (..), Sq (..))
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
  withIsPath2 :: IsPath qs => ((Ob (ps +++ qs)) => r) -> r
instance (Bicategory kk, Ob0 kk k) => IsPath (Nil :: Path kk k k) where
  singPath = SNil
  withIsPath2 r = r
instance (Ob0 kk i, Ob (p :: kk i j), IsPath (ps :: Path kk j k)) => IsPath (p ::: ps) where
  singPath = let p = obj @p in SCons p singPath
  withIsPath2 @qs = withIsPath2 @ps @qs

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
fold SNil = id
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
introI = Str SNil (SCons id SNil) id

elimI :: forall {kk} {j}. (Ob0 kk j, Bicategory kk) => (I ::: Nil) ~> (Nil :: Path kk j j)
elimI = Str (SCons id SNil) SNil id

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
  withOb2 @ps @qs = withIsPath2 @qs @ps
  r \\\ Str ps qs _ = withIsPath ps $ withIsPath qs r
  Str cs ds qs `o` Str as bs ps = Str (append as cs) (append bs ds) (concatFold bs ds . (qs `o` ps) . splitFold as cs)
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @p @q @r = obj @p `o` obj @q `o` obj @r
  associatorInv @p @q @r = obj @p `o` obj @q `o` obj @r

companionFold
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Companion hk (Fold fs) ~> Fold (Companion (Path hk) fs)
companionFold SNil = compToId
companionFold (SCons f SNil) = mapCompanion f
companionFold (SCons f fs@SCons{}) = let cfs = companionFold fs `o` mapCompanion @hk f in (cfs . compToCompose (fold fs) f) \\\ cfs

foldCompanion
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Fold (Companion (Path hk) fs) ~> Companion hk (Fold fs)
foldCompanion SNil = compFromId
foldCompanion (SCons f SNil) = mapCompanion f
foldCompanion (SCons f fs@SCons{}) = let cfs = foldCompanion fs `o` mapCompanion @hk f in (compFromCompose (fold fs) f . cfs) \\\ cfs

mapCompanionSPath
  :: forall hk {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> SPath (Companion (Path hk) fs)
mapCompanionSPath SNil = SNil
mapCompanionSPath (SCons f fs) = SCons (mapCompanion f) (mapCompanionSPath fs)

instance (HasCompanions hk vk) => HasCompanions (Path hk) (Path vk) where
  type Companion (Path hk) Nil = Nil
  type Companion (Path hk) (p ::: ps) = Companion hk p ::: Companion (Path hk) ps

  mapCompanion (Str fs gs n) =
    Str (mapCompanionSPath @hk fs) (mapCompanionSPath @hk gs) $ companionFold gs . mapCompanion @hk @vk n . foldCompanion fs

  compToId = Str SNil SNil id
  compFromId = Str SNil SNil id
  compToCompose (Str fs _ f) (Str gs _ g) =
    let cfs = mapCompanionSPath fs
        cgs = mapCompanionSPath gs
        fgs = append gs fs
    in Str (mapCompanionSPath fgs) (cgs `append` cfs) $
        concatFold cgs cfs
          . (companionFold fs `o` companionFold gs)
          . compToCompose f g
          . mapCompanion (splitFold gs fs)
          . foldCompanion fgs
  compFromCompose (Str fs _ f) (Str gs _ g) =
    let cfs = mapCompanionSPath fs
        cgs = mapCompanionSPath gs
        fgs = append gs fs
    in Str (cgs `append` cfs) (mapCompanionSPath fgs) $
        companionFold fgs
          . mapCompanion (concatFold gs fs)
          . compFromCompose f g
          . (foldCompanion fs `o` foldCompanion gs)
          . splitFold cgs cfs

mapConjointSPath
  :: forall hk {vk} {j} {k} (fs :: Path vk j k)
   . (Equipment hk vk)
  => SPath fs
  -> SPath (Conjoint (Path hk) fs)
mapConjointSPath SNil = SNil
mapConjointSPath (SCons f fs) = let fc = mapConjoint @hk f in mapConjointSPath fs `append` SCons fc SNil \\\ fc

instance (Equipment hk vk) => Equipment (Path hk) (Path vk) where
  type Conjoint (Path hk) Nil = Nil
  type Conjoint (Path hk) (p ::: ps) = Conjoint (Path hk) ps +++ (Conjoint hk p ::: Nil)

  mapConjoint n@(Str fsp gsp _) =
    let fs = src n
        gs = tgt n
        cfs = asObj (mapConjointSPath @hk fsp)
        cgs = asObj (mapConjointSPath @hk gsp)
        compN = mapCompanion n
    in rightUnitorWith (comConCounit @(Path hk) gs) cfs
        . associator' cfs (tgt compN) cgs
        . ((cfs `o` compN) `o` cgs)
        . leftUnitorInvWith (comConUnit fs) cgs

  comConUnit fs' = case asSPath fs' of
    SNil -> id
    SCons f sfs ->
      let fs = asObj sfs
          ls = mapCompanion @(Path hk) fs
          l = mapCompanion @hk f
          rs = mapConjoint @(Path hk) fs
          r = mapConjoint @hk f
          r' = singleton r
      in ( ((associatorInv' r' rs ls . (r' `o` comConUnit fs)) `o` singleton l)
            . elimO
            . singleton (comConUnit f)
            . introI
         )
          \\\ l
          \\\ r

  comConCounit fs' = case asSPath fs' of
    SNil -> id
    SCons @f f sfs ->
      let fs = asObj sfs
          ls = mapCompanion @(Path hk) fs
          l = mapCompanion @hk f
          l' = singleton l
          rs = mapConjoint @(Path hk) fs
          r = mapConjoint @hk f
          r' = singleton r
      in ( comConCounit fs
            . ( ls
                  `o` ( leftUnitorWith (elimI . singleton (comConCounit f) . introO @(Conjoint hk f) @(Companion hk f)) rs
                          . associatorInv' l' r' rs
                      )
              )
            . associator' ls l' (r' `o` rs)
         )
          \\\ rs
          \\\ l
          \\\ r

adjVK
  :: forall hk vk i j k f g v w x y
   . (Adjunction x v, Adjunction y w, HasCompanions hk vk, Ob v, Ob w)
  => RetroSq '(y :: hk i k, g) '(x, f :: vk j k)
  -> Sq '(v, g) '(w, f)
adjVK (RetroSq sq) =
  let cf = mapCompanion @(Path hk) (obj1 @f)
      cg = mapCompanion @(Path hk) (obj1 @g)
      v = obj1 @v
      w = obj1 @w
      x = obj1 @x
      y = obj1 @y
      counit' = str (x || v) iObj (counit @x @v)
      unit' = str iObj (w || y) (unit @y @w)
      sq' = str (y || cg) (cf || x) sq
  in Sq
      ( unStr
          ( unit' || cg || v
              == w || sq' || v
              == w || cf || counit'
          )
      )
      \\\ sq

adjHK
  :: forall hk vk i j k e f g h v w
   . (Adjunction f h, Adjunction g e, HasCompanions hk vk, Ob f, Ob g)
  => RetroSq '(v :: hk i k, h) '(w, e :: vk j k)
  -> Sq '(v, g) '(w, f)
adjHK (RetroSq sq) =
  let v = obj1 @v
      w = obj1 @w
      e = obj1 @e
      f = obj1 @f
      g = obj1 @g
      h = obj1 @h
      ce = mapCompanion @(Path hk) e
      cf = mapCompanion @(Path hk) f
      cg = mapCompanion @(Path hk) g
      ch = mapCompanion @(Path hk) h
      counit' = mapCompanion @(Path hk) (str (g || e) iObj (counit @g @e))
      unit' = mapCompanion @(Path hk) (str iObj (h || f) (unit @f @h))
      sq' = str (v || ch) (ce || w) sq
  in Sq
      ( unStr
          ( cg || v || unit'
              == cg || sq' || cf
              == counit' || w || cf
          )
      )
      \\\ sq

-- adj4Sq
--   :: forall hk vk i j k e f g h v w x y
--    . (Adjunction v x, Adjunction w y, Adjunction h f, Adjunction e g, HasCompanions hk vk)
--   => Sq '(v :: hk k j, g) '(w, f :: vk k i)
--   -> Sq '(y, h) '(x, e)
-- adj4Sq (Sq sq) =
--   let v = obj1 @v
--       w = obj1 @w
--       x = obj1 @x
--       y = obj1 @y
--       e = obj1 @e
--       f = obj1 @f
--       g = obj1 @g
--       h = obj1 @h
--       ce = mapCompanion @(Path hk) e
--       cf = mapCompanion @(Path hk) f
--       cg = mapCompanion @(Path hk) g
--       ch = mapCompanion @(Path hk) h
--       unitV = mapCompanion @(Path hk) (str iObj (f || h) (unit @h @f))
--       counitV = mapCompanion @(Path hk) (str (e || g) iObj (counit @e @g))
--       unitH = str iObj (x || v) (unit @v @x)
--       counitH = str (w || y) iObj (counit @w @y)
--       sq' = str (cg || v) (w || cf) sq
--   in Sq
--       ( unStr
--           ( (unitH == x || counitV || v) || ch || y
--               == x || ce || sq' || ch || y
--               == x || ce || (w || unitV || y == counitH)
--           )
--       )

instance (Bicategory kk, Ob0 kk a) => Monad (Nil :: Path kk a a) where
  eta = id
  mu = id

instance (Monad s, Ob s) => Monad (s ::: Nil) where
  eta = str iObj (obj1 @s) eta
  mu = str (obj1 @s || obj1 @s) (obj1 @s) mu

instance (Bicategory kk, Ob0 kk a) => Comonad (Nil :: Path kk a a) where
  epsilon = id
  delta = id

instance (Adjunction l r, Ob r, Ob l) => Monad (l ::: r ::: Nil) where
  eta = str iObj (obj1 @r || obj1 @l) (unit @l @r)
  mu = let r = obj1 @r; l = obj1 @l in r || str (l || r) iObj (counit @l @r) || l

instance (Adjunction l r, Ob r, Ob l) => Comonad (r ::: l ::: Nil) where
  epsilon = str (obj1 @l || obj1 @r) iObj (counit @l @r)
  delta = let r = obj1 @r; l = obj1 @l in l || str iObj (r || l) (unit @l @r) || r
