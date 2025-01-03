{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Category.Equipment where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Bicategory
  ( Adjunction (..)
  , Bicategory (..)
  , Ob'
  , Ob0'
  , associator'
  , associatorInv'
  , leftUnitorInvWith
  , leftUnitorWith
  , rightUnitorInvWith
  , rightUnitorWith
  , (==)
  , (||)
  )
import Proarrow.Category.Bicategory.Strictified
  ( Fold
  , Path (..)
  , SPath (..)
  , Strictified (Str)
  , append
  , asObj
  , asSPath
  , concatFold
  , elimI
  , elimO
  , fold
  , introI
  , introO
  , obj1
  , singleton
  , splitFold
  , str
  , unStr
  , type (+++)
  )
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), obj, src, tgt, (//), (\\), type (+->))
import Proarrow.Object (Obj)

infixl 6 |||
infixl 5 ===

-- | A double category with companions.
type HasCompanions :: forall {c}. CAT c -> CAT c -> Constraint
class (Bicategory hk, Bicategory vk, forall (k :: c). (Ob0 vk k) => Ob0' hk k) => HasCompanions (hk :: CAT c) vk | hk -> vk where
  -- All the data needed to make an id-on-objects (pseudo)functor Companion :: vk -> hk
  type Companion hk (f :: vk j k) :: hk j k
  mapCompanion :: forall {j} {k} (f :: vk j k) g. f ~> g -> Companion hk f ~> Companion hk g

  compToId :: (Ob0 vk k) => Companion hk (I :: vk k k) ~> (I :: hk k k)
  compFromId :: (Ob0 vk k) => (I :: hk k k) ~> Companion hk (I :: vk k k)

  compToCompose
    :: forall {j} {k} (f :: vk j k) g. Obj f -> Obj g -> Companion hk (f `O` g) ~> (Companion hk f `O` Companion hk g)
  compFromCompose
    :: forall {j} {k} (f :: vk j k) g. Obj f -> Obj g -> (Companion hk f `O` Companion hk g) ~> Companion hk (f `O` g)

class (Adjunction (Companion hk f) (Conjoint hk f)) => ComConAdjunction hk vk f
instance (Adjunction (Companion hk f) (Conjoint hk f)) => ComConAdjunction hk vk f

type Equipment :: forall {c}. CAT c -> CAT c -> Constraint
class (HasCompanions hk vk) => Equipment hk vk | hk -> vk where
  {-# MINIMAL mapConjoint, (conjToId, conjFromId, conjToCompose, conjFromCompose | comConUnit, comConCounit) #-}
  type Conjoint hk (f :: vk j k) :: hk k j
  mapConjoint :: forall {j} {k} (f :: vk j k) g. f ~> g -> Conjoint hk g ~> Conjoint hk f

  conjToId :: forall k. (Ob0 vk k) => Conjoint hk (I :: vk k k) ~> (I :: hk k k)
  conjToId = comConCounit iObj . leftUnitorInvWith compFromId (mapConjoint iObj)
  conjFromId :: forall k. (Ob0 vk k) => (I :: hk k k) ~> Conjoint hk (I :: vk k k)
  conjFromId = rightUnitorWith compToId (mapConjoint iObj) . comConUnit iObj

  conjToCompose
    :: forall {j} {k} (f :: vk j k) g. Obj f -> Obj g -> Conjoint hk (f `O` g) ~> (Conjoint hk g `O` Conjoint hk f)
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

  conjFromCompose
    :: forall {j} {k} (f :: vk j k) g. Obj f -> Obj g -> (Conjoint hk g `O` Conjoint hk f) ~> Conjoint hk (f `O` g)
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

  comConUnit :: forall {j} {k} (f :: vk j k). Obj f -> I ~> Conjoint hk f `O` Companion hk f
  default comConUnit
    :: forall {j} {k} (f :: vk j k). (((Ob f) => ComConAdjunction hk vk f)) => Obj f -> I ~> Conjoint hk f `O` Companion hk f
  comConUnit f = unit @(Companion hk f) @(Conjoint hk f) \\\ f
  comConCounit :: forall {j} {k} (f :: vk j k). Obj f -> Companion hk f `O` Conjoint hk f ~> I
  default comConCounit
    :: forall {j} {k} (f :: vk j k). ((Ob f) => ComConAdjunction hk vk f) => Obj f -> Companion hk f `O` Conjoint hk f ~> I
  comConCounit f = counit @(Companion hk f) @(Conjoint hk f) \\\ f

-- | P(f, g)
type Cart (p :: hk h j) (f :: vk h i) (g :: vk j k) = Companion hk g `O` p `O` Conjoint hk f

-- | The kind of a square @'(q, f) '(p, g)@.
--
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--g--k
type SQ' (hk :: CAT c) (vk :: CAT c) h i j k = (hk k i, vk j k) +-> (hk j h, vk h i)

type SQ (hk :: CAT c) (vk :: CAT c) = forall {h} {i} {j} {k}. SQ' hk vk h i j k

type Sq :: forall {c} {hk :: CAT c} {vk :: CAT c}. SQ hk vk
data Sq pf qg where
  Sq
    :: forall {hk} {vk} {h} {i} {j} {k} (p :: hk j h) (q :: hk k i) (f :: vk h i) (g :: vk j k)
     . (Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob p, Ob q, Ob f, Ob g)
    => Companion hk f `O` p ~> q `O` Companion hk g
    -> Sq '(p, f) '(q, g)

instance (HasCompanions hk vk, Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k) => Profunctor (Sq :: SQ' hk vk h i j k) where
  dimap (p :**: f) (q :**: g) (Sq sq) = Sq (mapCompanion f || p == sq == q || mapCompanion g) \\\ p \\\ q \\\ f \\\ g
  r \\ Sq sq = r \\ sq

-- | The empty square for an object.
--
-- > k-----k
-- > |     |
-- > |     |
-- > |     |
-- > k-----k
object :: (HasCompanions hk vk, Ob0 vk k) => Sq '(I :: hk k k, I :: vk k k) '(I, I)
object = hArr iObj

-- | Make a square from a horizontal arrow
--
-- > k-----k
-- > |     |
-- > p--@--q
-- > |     |
-- > j-----j
hArr
  :: forall {hk} {vk} {j} {k} (p :: hk j k) q
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => p ~> q
  -> Sq '(p, I :: vk k k) '(q, I :: vk j j)
hArr n =
  Sq (rightUnitorInvWith (compFromId @hk @vk) (tgt n) . n . leftUnitorWith (compToId @hk @vk) (src n))
    \\ n
    \\ iObj @vk @j
    \\ iObj @vk @k

-- > j-----j
-- > |     |
-- > p-----p
-- > |     |
-- > k-----k
hId :: (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (p :: hk k j)) => Sq '(p, I :: vk j j) '(p, I :: vk k k)
hId = hArr id

-- > k-----k
-- > |     |
-- > f>--->f
-- > |     |
-- > j-----j
compId
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Companion hk f, I :: vk k k) '(Companion hk f, I :: vk j j)
compId = hArr (mapCompanion @hk (obj @f))

-- > j-----j
-- > |     |
-- > f>--->f
-- > |     |
-- > k-----k
conjId
  :: forall {hk} {vk} {j} {k} f
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk f, I :: vk j j) '(Conjoint hk f, I :: vk k k)
conjId = hArr (mapConjoint @hk (obj @f))

-- | Make a square from a vertical arrow
--
-- > j--f--k
-- > |  v  |
-- > |  @  |
-- > |  v  |
-- > j--g--k
vArr
  :: forall {hk} {vk} {j} {k} (f :: vk j k) g
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k)
  => f ~> g
  -> Sq '(I :: hk j j, f) '(I :: hk k k, g)
vArr n =
  let n' = mapCompanion @hk @vk n
  in Sq (leftUnitorInv . n' . rightUnitor) \\ n \\ n' \\ iObj @hk @j \\ iObj @hk @k

-- > j--f--k
-- > |  v  |
-- > |  |  |
-- > |  v  |
-- > j--f--k
vId
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (HasCompanions hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(I :: hk j j, f) '(I :: hk k k, f)
vId = vArr id

-- | Horizontal composition
--
-- > l--d--h     h--f--i     l-f∘d-i
-- > |  v  |     |  v  |     |  v  |
-- > p--@--q ||| q--@--r  =  p--@--r
-- > |  v  |     |  v  |     |  v  |
-- > m--e--j     j--g--k     m-g∘e-k
(|||)
  :: forall {hk} {vk} {h} {l} {m} (p :: hk m l) q r (d :: vk l h) e f g
   . (HasCompanions hk vk)
  => Sq '(p, d) '(q, e)
  -> Sq '(q, f) '(r, g)
  -> Sq '(p, f `O` d) '(r, g `O` e)
Sq sqL ||| Sq sqR =
  ( let d = obj @d
        e = obj @e
        f = obj @f
        g = obj @g
        dc = mapCompanion @hk d
        ec = mapCompanion @hk e
        fc = mapCompanion @hk f
        gc = mapCompanion @hk g
    in (g `o` e) // (f `o` d) // dc // ec // fc // gc // Sq $
        (obj @r `o` compFromCompose g e)
          . associator @_ @r @(Companion hk g) @(Companion hk e)
          . (sqR `o` obj @(Companion hk e))
          . associatorInv @_ @(Companion hk f) @q @(Companion hk e)
          . (obj @(Companion hk f) `o` sqL)
          . associator @_ @(Companion hk f) @(Companion hk d) @p
          . (compToCompose f d `o` obj @p)
  )
    \\\ sqL
    \\\ sqR

-- | Vertical composition
--
-- >  h--e--i
-- >  |  v  |
-- >  r--@--s
-- >  |  v  |
-- >  j--f--k
-- >    ===
-- >  j--f--k
-- >  |  v  |
-- >  p--@--q
-- >  |  v  |
-- >  l--g--m
-- >
-- >    v v
-- >
-- >  h--e--i
-- >  |  v  |
-- > r∘p-@-s∘q
-- >  |  v  |
-- >  j--g--k
(===)
  :: forall {hk} {vk} {h} {i} {j} {l} (p :: hk l j) q r s (e :: vk h i) f g
   . (HasCompanions hk vk)
  => Sq '(r, e) '(s, f)
  -> Sq '(p, f) '(q, g)
  -> Sq '(r `O` p, e) '(s `O` q, g)
Sq sqL === Sq sqR =
  ( let p = obj @p
        q = obj @q
        r = obj @r
        s = obj @s
        ec = mapCompanion @hk (obj @e)
        fc = mapCompanion @hk (obj @f)
        gc = mapCompanion @hk (obj @g)
    in (r `o` p) // (s `o` q) // ec // fc // gc // Sq $
        associatorInv @_ @s @q @(Companion hk g)
          . (s `o` sqR)
          . associator @_ @s @(Companion hk f) @p
          . (sqL `o` p)
          . associatorInv @_ @(Companion hk e) @r @p
  )
    \\\ sqL
    \\\ sqR

-- > j--f--k
-- > |  v  |
-- > |  \->f
-- > |     |
-- > j-----j
toRight
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob' (f :: vk j k))
  => Sq '(I :: hk j j, f) '(Companion hk f, I :: vk j j)
toRight = let comp = mapCompanion @hk @vk (obj @f) in Sq (comp `o` compFromId) \\ comp \\ iObj @hk @j \\ iObj @vk @j

-- > k-----k
-- > |     |
-- > f>-\  |
-- > |  v  |
-- > j--f--k
fromLeft
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob' (f :: vk j k))
  => Sq '(Companion hk f, I :: vk k k) '(I :: hk k k, f)
fromLeft = let comp = mapCompanion @hk @vk (obj @f) in Sq (compToId `o` comp) \\ comp \\ iObj @hk @k \\ iObj @vk @k

-- > j-----j
-- > |     |
-- > |  /-<f
-- > |  v  |
-- > j--f--k
fromRight
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob f)
  => Sq '(I :: hk j j, I :: vk j j) '(Conjoint hk f, f)
fromRight =
  let f = obj @f
  in Sq (comConUnit @hk @vk f . leftUnitorWith (compToId @hk @vk) iObj)
      \\\ mapConjoint @hk @vk f
      \\ iObj @hk @j
      \\ iObj @vk @j

-- > j--f--k
-- > |  v  |
-- > f<-/  |
-- > |     |
-- > k-----k
toLeft
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, Ob0 vk j, Ob0 vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk f, f) '(I :: hk k k, I :: vk k k)
toLeft =
  let f = obj @f
  in Sq (rightUnitorInvWith (compFromId @hk @vk) iObj . comConCounit @hk @vk f)
      \\\ mapConjoint @hk @vk f
      \\ iObj @hk @k
      \\ iObj @vk @k

flipCompanion
  :: forall {j} {k} hk vk (f :: vk j k) p q
   . (Equipment hk vk, Ob p)
  => Obj f
  -> Companion hk f `O` p ~> q
  -> p ~> Conjoint hk f `O` q
flipCompanion f n =
  let comF = mapCompanion @hk f; conF = mapConjoint @hk f
  in ((conF `o` n) . associator' conF comF (obj @p) . leftUnitorInvWith (comConUnit f) id) \\\ n \\\ f

flipCompanionInv
  :: forall {j} {k} hk vk (f :: vk j k) p q
   . (Equipment hk vk, Ob q)
  => Obj f
  -> p ~> Conjoint hk f `O` q
  -> Companion hk f `O` p ~> q
flipCompanionInv f n =
  let comF = mapCompanion @hk f; conF = mapConjoint @hk f
  in (leftUnitorWith (comConCounit f) id . associatorInv' comF conF (obj @q) . (comF `o` n)) \\\ n \\\ f

flipConjoint
  :: forall {j} {k} hk vk (f :: vk j k) p q
   . (Equipment hk vk, Ob p)
  => Obj f
  -> p `O` Conjoint hk f ~> q
  -> p ~> q `O` Companion hk f
flipConjoint f n =
  let comF = mapCompanion @hk f; conF = mapConjoint @hk f
  in ((n `o` comF) . associatorInv' (obj @p) conF comF . rightUnitorInvWith (comConUnit f) id) \\\ n \\\ f

flipConjointInv
  :: forall {j} {k} hk vk (f :: vk j k) p q
   . (Equipment hk vk, Ob q)
  => Obj f
  -> p ~> q `O` Companion hk f
  -> p `O` Conjoint hk f ~> q
flipConjointInv f n =
  let comF = mapCompanion @hk f; conF = mapConjoint @hk f
  in (rightUnitorWith (comConCounit f) id . associator' (obj @q) comF conF . (n `o` conF)) \\\ n \\\ f

-- |
-- The kind of a retro square @'(q, f) '(p, g)@.
--
-- > h--f--i
-- > |  v  |
-- > p--§--q
-- > |  v  |
-- > j--g--k
type RetroSq :: forall {c} {hk :: CAT c} {vk :: CAT c} {h} {i} {j} {k}. (hk j h, vk h i) +-> (hk k i, vk j k)
data RetroSq pf qg where
  RetroSq
    :: forall {hk} {vk} {h} {i} {j} {k} (p :: hk j h) (q :: hk k i) (f :: vk h i) (g :: vk j k)
     . (Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k, Ob p, Ob q, Ob f, Ob g)
    => (q `O` Companion hk g) ~> Companion hk f `O` p
    -> RetroSq '(q, g) '(p, f)

instance
  (HasCompanions hk vk, Ob0 vk h, Ob0 vk i, Ob0 vk j, Ob0 vk k)
  => Profunctor (RetroSq :: (hk j h, vk h i) +-> (hk k i, vk j k))
  where
  dimap (q :**: f) (p :**: g) (RetroSq sq) = RetroSq (q || mapCompanion f == sq == mapCompanion g || p) \\\ p \\\ q \\\ f \\\ g
  r \\ RetroSq sq = r \\ sq

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
      in ( ((associatorInv' r' rs ls . (r' `o` comConUnit @(Path hk) fs)) `o` singleton l)
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

-- adjHK
--   :: forall hk vk i j k e f g h v w
--    . (Adjunction h f, Adjunction e g, HasCompanions hk vk)
--   => RetroSq '(v :: hk i k, h) '(w, e :: vk j k)
--   -> Sq '(v, g) '(w, f)
-- adjHK (RetroSq sq) =
--   let v = obj1 @v
--       w = obj1 @w
--       e = obj1 @e
--       f = obj1 @f
--       g = obj1 @g
--       h = obj1 @h
--       ce = mapCompanion @(Path hk) e
--       cf = mapCompanion @(Path hk) f
--       cg = mapCompanion @(Path hk) g
--       ch = mapCompanion @(Path hk) h
--       unit' = mapCompanion @(Path hk) (str iObj (g || e) (unit @e @g))
--       counit' = mapCompanion @(Path hk) (str (h || f) iObj (counit @h @f))
--       sq' = str (v || ch) (ce || w) sq
--   in Sq
--       ( unStr
--           ( cg || v || counit'
--               == cg || sq' || cf
--               == unit' || w || cf
--           )
--       )
--       \\\ sq

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
