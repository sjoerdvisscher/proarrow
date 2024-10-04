{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Category.Equipment where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Bicategory
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Core (CAT, CategoryOf (..), PRO, Profunctor (..), Promonad (..), obj, src, tgt, (//), (\\))
import Proarrow.Object (Obj)

infixl 6 |||
infixl 5 ===

class (Ob0 kk k) => Ob0' kk k
instance (Ob0 kk k) => Ob0' kk k

-- | A double category with companions.
type HasCompanions :: forall {c}. CAT c -> CAT c -> Constraint
class (Bicategory hk, Bicategory vk, forall (k :: c). (Ob0 vk k) => Ob0' hk k) => HasCompanions (hk :: CAT c) vk | hk -> vk where
  -- All the data needed to make an id-on-objects (pseudo)functor Companion :: vk -> hk
  type Companion hk vk (f :: vk j k) :: hk j k
  mapCompanion :: f ~> g -> Companion hk vk g ~> Companion hk vk f

  compToId :: (Ob0 vk k) => Companion hk vk (I :: vk k k) ~> (I :: hk k k)
  compFromId :: (Ob0 vk k) => (I :: hk k k) ~> Companion hk vk (I :: vk k k)

  compToCompose :: Obj f -> Obj g -> Companion hk vk (f `O` g) ~> (Companion hk vk f `O` Companion hk vk g)
  compFromCompose :: Obj f -> Obj g -> (Companion hk vk f `O` Companion hk vk g) ~> Companion hk vk (f `O` g)

-- |
-- The kind of a square @'(p, f) '(q, g)@.
--
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--g--k
type SQ' (hk :: CAT c) (vk :: CAT c) h i j k = PRO (hk h j, vk h i) (hk i k, vk j k)

type SQ (hk :: CAT c) (vk :: CAT c) = forall {h} {i} {j} {k}. SQ' hk vk h i j k

type Sq :: forall {c} {hk :: CAT c} {vk :: CAT c}. SQ hk vk
data Sq pf qg where
  Sq
    :: forall {hk} {vk} {h} {i} {j} {k} (p :: hk h j) (q :: hk i k) (f :: vk h i) (g :: vk j k)
     . (Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob p, Ob q, Ob f, Ob g)
    => (Companion hk vk g `O` p) ~> q `O` Companion hk vk f
    -> Sq '(p, f) '(q, g)

instance (HasCompanions hk vk, Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k) => Profunctor (Sq :: SQ' hk vk h i j k) where
  dimap (p :**: f) (q :**: g) (Sq sq) = Sq ((q `o` mapCompanion f) . sq . (mapCompanion g `o` p)) \\\ p \\\ q \\\ f \\\ g
  r \\ Sq sq = r \\ sq

-- | The empty square for an object.
object :: (HasCompanions hk vk, Ob0 vk k) => Sq '(I :: hk k k, I :: vk k k) '(I, I)
object = hArr iObj

-- | Make a square from a horizontal arrow
hArr
  :: forall {hk} {vk} {j} {k} (p :: hk j k) q
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => p ~> q
  -> Sq '(p, I :: vk j j) '(q, I :: vk k k)
hArr n =
  Sq (rightUnitorInvWith (compFromId @hk @vk) (tgt n) . n . leftUnitorWith (compToId @hk @vk) (src n))
    \\ n
    \\ iObj @vk @j
    \\ iObj @vk @k

-- | Horizontal composition
(|||)
  :: forall {hk} {vk} {h} {i} {j} {k} {l} p q r f g d e
   . (HasCompanions hk vk)
  => Sq '(p :: hk h j, f :: vk h i) '(q, g)
  -> Sq '(q :: hk i k, d :: vk i l) '(r, e)
  -> Sq '(p, d `O` f) '(r, e `O` g)
Sq sqL ||| Sq sqR =
  ( let p = obj @p
        q = obj @q
        r = obj @r
        d = obj @d
        e = obj @e
        f = obj @f
        g = obj @g
        dc = mapCompanion @hk d
        ec = mapCompanion @hk e
        fc = mapCompanion @hk f
        gc = mapCompanion @hk g
    in (d `o` f) // (e `o` g) // Sq $
        (r `o` compFromCompose d f)
          . associator r dc fc
          . (sqR `o` fc)
          . associatorInv ec q fc
          . (ec `o` sqL)
          . associator ec gc p
          . (compToCompose e g `o` p)
  )
    \\\ sqL
    \\\ sqR

-- | Make a square from a vertical arrow
vArr
  :: forall {hk} {vk} {j} {k} (f :: vk j k) g
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => f ~> g
  -> Sq '(I :: hk j j, f) '(I :: hk k k, g)
vArr n =
  let n' = mapCompanion @hk @vk n
  in Sq (leftUnitorInv (tgt n') . n' . rightUnitor (src n')) \\ n \\ iObj @hk @j \\ iObj @hk @k

-- | Vertical composition
(===)
  :: forall {hk} {vk} {h} {i} {j} {k} {l} p q r s f g e
   . (HasCompanions hk vk)
  => Sq '(p :: hk h j, f :: vk h i) '(q, g)
  -> Sq '(r :: hk j k, g :: vk j l) '(s, e)
  -> Sq '(r `O` p, f) '(s `O` q, e)
Sq sqL === Sq sqR =
  ( let p = obj @p
        q = obj @q
        r = obj @r
        s = obj @s
        ec = mapCompanion @hk (obj @e)
        fc = mapCompanion @hk (obj @f)
        gc = mapCompanion @hk (obj @g)
    in (r `o` p) // (s `o` q) // Sq $
        associatorInv s q fc
          . (s `o` sqL)
          . associator s gc p
          . (sqR `o` p)
          . associatorInv ec r p
  )
    \\\ sqL
    \\\ sqR

fromRight
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(I :: hk j j, I :: vk j j) '(Companion hk vk f, f)
fromRight = let comp = mapCompanion @hk @vk (obj @f) in Sq (comp `o` compFromId) \\ comp \\ iObj @hk @j \\ iObj @vk @j

toLeft
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Companion hk vk f, f) '(I :: hk k k, I :: vk k k)
toLeft = let comp = mapCompanion @hk @vk (obj @f) in Sq (compToId `o` comp) \\ comp \\ iObj @hk @k \\ iObj @vk @k

toRight
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob f)
  => Sq '(I :: hk j j, f) '(Conjoint hk vk f, I :: vk j j)
toRight =
  let f = obj @f
  in Sq (comConUnit @hk @vk f . leftUnitorWith (compToId @hk @vk) iObj)
      \\\ mapConjoint @hk @vk f
      \\ iObj @hk @j
      \\ iObj @vk @j

fromLeft
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk vk f, I :: vk k k) '(I :: hk k k, f)
fromLeft =
  let f = obj @f
  in Sq (rightUnitorInvWith (compFromId @hk @vk) iObj . comConCounit @hk @vk f)
      \\\ mapConjoint @hk @vk f
      \\ iObj @hk @k
      \\ iObj @vk @k

flipCompanion
  :: forall hk vk f p q. (Equipment hk vk, Ob p) => Obj f -> Companion hk vk f `O` p ~> q -> p ~> Conjoint hk vk f `O` q
flipCompanion f n =
  ((mapConjoint f `o` n) . associator (mapConjoint f) (mapCompanion f) (obj @p) . leftUnitorInvWith (comConUnit f) id)
    \\\ n
    \\\ f

flipCompanionInv
  :: forall hk vk f p q. (Equipment hk vk, Ob q) => Obj f -> p ~> Conjoint hk vk f `O` q -> Companion hk vk f `O` p ~> q
flipCompanionInv f n =
  (leftUnitorWith (comConCounit f) id . associatorInv (mapCompanion f) (mapConjoint f) (obj @q) . (mapCompanion f `o` n))
    \\\ n
    \\\ f

flipConjoint
  :: forall hk vk f p q. (Equipment hk vk, Ob p) => Obj f -> p `O` Conjoint hk vk f ~> q -> p ~> q `O` Companion hk vk f
flipConjoint f n =
  ( (n `o` mapCompanion f) . associatorInv (obj @p) (mapConjoint f) (mapCompanion f) . rightUnitorInvWith (comConUnit f) id
  )
    \\\ n
    \\\ f

flipConjointInv
  :: forall hk vk f p q. (Equipment hk vk, Ob q) => Obj f -> p ~> q `O` Companion hk vk f -> p `O` Conjoint hk vk f ~> q
flipConjointInv f n =
  (rightUnitorWith (comConCounit f) id . associator (obj @q) (mapCompanion f) (mapConjoint f) . (n `o` mapConjoint f))
    \\\ n
    \\\ f

class (Adjunction (Companion hk vk f) (Conjoint hk vk f)) => ComConAdjunction hk vk f
instance (Adjunction (Companion hk vk f) (Conjoint hk vk f)) => ComConAdjunction hk vk f

type Equipment :: forall {c}. CAT c -> CAT c -> Constraint
class (HasCompanions hk vk) => Equipment hk vk where
  type Conjoint hk vk (f :: vk j k) :: hk k j
  mapConjoint :: f ~> g -> Conjoint hk vk f ~> Conjoint hk vk g

  conjToId :: forall k. (Ob0 vk k) => Conjoint hk vk (I :: vk k k) ~> (I :: hk k k)
  conjToId = comConCounit iObj . leftUnitorInvWith compFromId (mapConjoint iObj)
  conjFromId :: forall k. (Ob0 vk k) => (I :: hk k k) ~> Conjoint hk vk (I :: vk k k)
  conjFromId = rightUnitorWith compToId (mapConjoint iObj) . comConUnit iObj

  conjToCompose :: Obj f -> Obj g -> Conjoint hk vk (f `O` g) ~> (Conjoint hk vk g `O` Conjoint hk vk f)
  conjToCompose f g =
    unStr
      ( let
          fg = f `o` g
          comFG = singleton (mapCompanion @hk fg)
          comF = singleton (mapCompanion @hk f)
          comG = singleton (mapCompanion @hk g)
          conFG = singleton (mapConjoint @hk fg)
          conF = singleton (mapConjoint @hk f)
          conG = singleton (mapConjoint @hk g)
          counitFG = str (comFG || conFG) iObj (comConCounit fg)
          compFG = str (comF || comG) comFG (compFromCompose f g)
          unitF = str iObj (conF || comF) (comConUnit f)
          unitG = str iObj (conG || comG) (comConUnit g)
        in
          (unitG == conG || unitF || comG) || conFG
            == conG || conF || (compFG || conFG == counitFG)
      )
      \\\ f
      \\\ g

  conjFromCompose :: Obj f -> Obj g -> (Conjoint hk vk g `O` Conjoint hk vk f) ~> Conjoint hk vk (f `O` g)
  conjFromCompose f g =
    unStr
      ( let
          fg = f `o` g
          comFG = singleton (mapCompanion @hk fg)
          comF = singleton (mapCompanion @hk f)
          comG = singleton (mapCompanion @hk g)
          conFG = singleton (mapConjoint @hk fg)
          conF = singleton (mapConjoint @hk f)
          conG = singleton (mapConjoint @hk g)
          counitF = str (comF || conF) iObj (comConCounit f)
          counitG = str (comG || conG) iObj (comConCounit g)
          compFG = str comFG (comF || comG) (compToCompose f g)
          unitFG = str iObj (conFG || comFG) (comConUnit fg)
        in
          (unitFG == conFG || compFG) || conG || conF
            == conFG || (comF || counitG || conF == counitF)
      )
      \\\ f
      \\\ g

  comConUnit :: Obj f -> I ~> Conjoint hk vk f `O` Companion hk vk f
  default comConUnit
    :: forall f. (((Ob f) => ComConAdjunction hk vk f)) => Obj f -> I ~> Conjoint hk vk f `O` Companion hk vk f
  comConUnit f = unit @(Companion hk vk f) @(Conjoint hk vk f) \\\ f
  comConCounit :: Obj f -> Companion hk vk f `O` Conjoint hk vk f ~> I
  default comConCounit
    :: forall f. ((Ob f) => ComConAdjunction hk vk f) => Obj f -> Companion hk vk f `O` Conjoint hk vk f ~> I
  comConCounit f = counit @(Companion hk vk f) @(Conjoint hk vk f) \\\ f

-- | P(f, g)
type Cart (p :: hk b d) (f :: vk a b) (g :: vk c d) = Conjoint hk vk g `O` p `O` Companion hk vk f

companionFold
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Companion hk vk (Fold fs) ~> Fold (Companion (Path hk) (Path vk) fs)
companionFold SNil = compToId
companionFold (SCons f SNil) = mapCompanion f
companionFold (SCons f fs@SCons{}) = let cfs = companionFold fs `o` mapCompanion @hk f in (cfs . compToCompose (fold fs) f) \\\ cfs

foldCompanion
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Fold (Companion (Path hk) (Path vk) fs) ~> Companion hk vk (Fold fs)
foldCompanion SNil = compFromId
foldCompanion (SCons f SNil) = mapCompanion f
foldCompanion (SCons f fs@SCons{}) = let cfs = foldCompanion fs `o` mapCompanion @hk f in (compFromCompose (fold fs) f . cfs) \\\ cfs

mapCompanionSPath
  :: forall hk {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> SPath (Companion (Path hk) (Path vk) fs)
mapCompanionSPath SNil = SNil
mapCompanionSPath (SCons f fs) = SCons (mapCompanion f) (mapCompanionSPath fs)

instance (HasCompanions hk vk) => HasCompanions (Path hk) (Path vk) where
  type Companion (Path hk) (Path vk) Nil = Nil
  type Companion (Path hk) (Path vk) (p ::: ps) = Companion hk vk p ::: Companion (Path hk) (Path vk) ps

  mapCompanion (Str fs gs n) =
    Str (mapCompanionSPath @hk gs) (mapCompanionSPath @hk fs) $ companionFold fs . mapCompanion @hk @vk n . foldCompanion gs

  compToId = Str SNil SNil iObj
  compFromId = Str SNil SNil iObj
  compToCompose (Str fs _ f) (Str gs _ g) =
    let cfs = mapCompanionSPath fs
        cgs = mapCompanionSPath gs
        fgs = append gs fs
    in Str (mapCompanionSPath fgs) (cgs `append` cfs) $
        concatFold cgs cfs
          . (companionFold fs `o` companionFold gs)
          . compToCompose f g
          . mapCompanion (concatFold gs fs)
          . foldCompanion fgs
  compFromCompose (Str fs _ f) (Str gs _ g) =
    let cfs = mapCompanionSPath fs
        cgs = mapCompanionSPath gs
        fgs = append gs fs
    in Str (cgs `append` cfs) (mapCompanionSPath fgs) $
        companionFold fgs
          . mapCompanion (splitFold gs fs)
          . compFromCompose f g
          . (foldCompanion fs `o` foldCompanion gs)
          . splitFold cgs cfs

mapConjointSPath
  :: forall hk {vk} {j} {k} (fs :: Path vk j k)
   . (Equipment hk vk)
  => SPath fs
  -> SPath (Conjoint (Path hk) (Path vk) fs)
mapConjointSPath SNil = SNil
mapConjointSPath (SCons f fs) = let fc = mapConjoint @hk f in mapConjointSPath fs `append` SCons fc SNil \\\ fc

instance (Equipment hk vk) => Equipment (Path hk) (Path vk) where
  type Conjoint (Path hk) (Path vk) Nil = Nil
  type Conjoint (Path hk) (Path vk) (p ::: ps) = Conjoint (Path hk) (Path vk) ps +++ (Conjoint hk vk p ::: Nil)

  mapConjoint n@(Str fsp gsp _) =
    let fs = src n
        gs = tgt n
        cfs = asObj (mapConjointSPath @hk fsp)
        cgs = asObj (mapConjointSPath @hk gsp)
        compN = mapCompanion n
    in rightUnitorWith (comConCounit @(Path hk) fs) cgs
        . associator cgs (tgt compN) cfs
        . ((cgs `o` compN) `o` cfs)
        . leftUnitorInvWith (comConUnit gs) cfs

  comConUnit fs' = case asSPath fs' of
    SNil -> id
    SCons f sfs ->
      let fs = asObj sfs
          ls = mapCompanion @(Path hk) fs
          l = mapCompanion @hk f
          rs = mapConjoint @(Path hk) fs
          r = mapConjoint @hk f
          r' = singleton r
      in ( ((associatorInv r' rs ls . (r' `o` comConUnit @(Path hk) fs)) `o` singleton l)
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
                  `o` ( leftUnitorWith (elimI . singleton (comConCounit f) . introO @(Conjoint hk vk f) @(Companion hk vk f)) rs
                          . associatorInv l' r' rs
                      )
              )
            . associator ls l' (r' `o` rs)
         )
          \\\ rs
          \\\ l
          \\\ r

-- |
-- The kind of a retro square @'(q, g) '(p, f)@.
--
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--g--k
type RetroSq :: forall {c} {hk :: CAT c} {vk :: CAT c} {h} {i} {j} {k}. PRO (hk i k, vk j k) (hk h j, vk h i)
data RetroSq pf qg where
  RetroSq
    :: forall {hk} {vk} {h} {i} {j} {k} (p :: hk h j) (q :: hk i k) (f :: vk h i) (g :: vk j k)
     . (Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob p, Ob q, Ob f, Ob g)
    => (q `O` Companion hk vk f) ~> Companion hk vk g `O` p
    -> RetroSq '(q, g) '(p, f)

instance
  (HasCompanions hk vk, Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k)
  => Profunctor (RetroSq :: PRO (hk i k, vk j k) (hk h j, vk h i))
  where
  dimap (q :**: g) (p :**: f) (RetroSq sq) = RetroSq ((mapCompanion g `o` p) . sq . (q `o` mapCompanion f)) \\\ p \\\ q \\\ f \\\ g
  r \\ RetroSq sq = r \\ sq

adjVK
  :: forall hk vk i j k f g v w x y
   . (Adjunction x v, Adjunction y w, HasCompanions hk vk)
  => RetroSq '(y :: hk i k, f :: vk j k) '(x, g)
  -> Sq '(v, f) '(w, g)
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
   . (Adjunction h f, Adjunction e g, HasCompanions hk vk)
  => RetroSq '(v :: hk i k, e :: vk j k) '(w, h)
  -> Sq '(v, f) '(w, g)
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
      unit' = mapCompanion @(Path hk) (str iObj (g || e) (unit @e @g))
      counit' = mapCompanion @(Path hk) (str (h || f) iObj (counit @h @f))
      sq' = str (v || ch) (ce || w) sq
  in Sq
      ( unStr
          ( cg || v || counit'
              == cg || sq' || cf
              == unit' || w || cf
          )
      )
      \\\ sq

adj4Sq
  :: forall hk vk i j k e f g h v w x y
   . (Adjunction v x, Adjunction w y, Adjunction h f, Adjunction e g, HasCompanions hk vk)
  => Sq '(v :: hk k j, f :: vk k i) '(w, g)
  -> Sq '(y, e) '(x, h)
adj4Sq (Sq sq) =
  let v = obj1 @v
      w = obj1 @w
      x = obj1 @x
      y = obj1 @y
      e = obj1 @e
      f = obj1 @f
      g = obj1 @g
      h = obj1 @h
      ce = mapCompanion @(Path hk) e
      cf = mapCompanion @(Path hk) f
      cg = mapCompanion @(Path hk) g
      ch = mapCompanion @(Path hk) h
      unitV = mapCompanion @(Path hk) (str iObj (f || h) (unit @h @f))
      counitV = mapCompanion @(Path hk) (str (e || g) iObj (counit @e @g))
      unitH = str iObj (x || v) (unit @v @x)
      counitH = str (w || y) iObj (counit @w @y)
      sq' = str (cg || v) (w || cf) sq
  in Sq
      ( unStr
          ( (unitH == x || counitV || v) || ch || y
              == x || ce || sq' || ch || y
              == x || ce || (w || unitV || y == counitH)
          )
      )
