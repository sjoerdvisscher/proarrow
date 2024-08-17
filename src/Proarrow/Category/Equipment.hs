{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Category.Equipment where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Bicategory
import Proarrow.Category.Bicategory.Co (COK (CO), Co (..))
import Proarrow.Category.Bicategory.Op (OPK (OP), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Core (CAT, CategoryOf (..), PRO, Profunctor (..), Promonad (..), UN, obj, src, tgt, (//), (\\))
import Proarrow.Object (Obj)

infixl 6 |||
infixl 5 ===

class (Ob0 kk k) => Ob0' kk k
instance (Ob0 kk k) => Ob0' kk k

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

type Sq :: forall {c} {hk :: CAT c} {vk :: CAT c}. SQ hk vk
data Sq pf qg where
  Sq
    :: forall {hk} {vk} {h} {i} {j} {k} (p :: hk h j) (q :: hk i k) (f :: vk h i) (g :: vk j k)
     . (DOb hk vk h, DOb hk vk i, DOb hk vk j, DOb hk vk k, Ob p, Ob q, Ob f, Ob g)
    => (p `O` Companion hk vk g) ~> Companion hk vk f `O` q
    -> Sq '(p, f) '(q, g)

instance (HasCompanions hk vk, DOb hk vk h, DOb hk vk i, DOb hk vk j, DOb hk vk k) => Profunctor (Sq :: SQ' hk vk h i j k) where
  dimap (p :**: f) (q :**: g) (Sq sq) = Sq ((mapCompanion f `o` q) . sq . (p `o` mapCompanion g)) \\\ p \\\ q \\\ f \\\ g
  r \\ Sq sq = r \\ sq

type DOb hk vk k = (Ob0 hk k, Ob0 vk k)

-- | The empty square for an object.
object :: (HasCompanions hk vk, DOb hk vk k) => Sq '(I :: hk k k, I :: vk k k) '(I, I)
object = hArr iObj

-- | Make a square from a horizontal arrow
hArr
  :: forall {hk} {vk} {j} {k} (p :: hk j k) q
   . (HasCompanions hk vk, DOb hk vk j, DOb hk vk k)
  => p ~> q
  -> Sq '(p, I :: vk j j) '(q, I :: vk k k)
hArr n =
  Sq (leftUnitorInvWith (compFromId @hk @vk) (tgt n) . n . rightUnitorWith (compToId @hk @vk) (src n)) \\ n \\ iObj @vk @j \\ iObj @vk @k

-- | Horizontal composition
(|||)
  :: forall {hk} {vk} {h} {i} {j} {k} {l} p q r f g d e
   . (HasCompanions hk vk)
  => Sq '(p :: hk h j, f :: vk h i) '(q, g)
  -> Sq '(q :: hk i k, d :: vk i l) '(r, e)
  -> Sq '(p, f `O` d) '(r, g `O` e)
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
    in (f `o` d) // (g `o` e) // Sq $
        (compFromCompose f d `o` r)
          . associatorInv fc dc r
          . (fc `o` sqR)
          . associator fc q ec
          . (sqL `o` ec)
          . associatorInv p gc ec
          . (p `o` compToCompose g e)
  )
    \\\ sqL
    \\\ sqR

-- | Make a square from a vertical arrow
vArr
  :: forall {hk} {vk} {j} {k} (f :: vk j k) g
   . (HasCompanions hk vk, DOb hk vk j, DOb hk vk k)
  => f ~> g
  -> Sq '(I :: hk j j, f) '(I :: hk k k, g)
vArr n = let n' = mapCompanion @hk @vk n in Sq (rightUnitorInv (tgt n') . n' . leftUnitor (src n')) \\ n \\ iObj @hk @j \\ iObj @hk @k

-- | Vertical composition
(===)
  :: forall {hk} {vk} {h} {i} {j} {k} {l} p q r s f g e
   . (HasCompanions hk vk)
  => Sq '(p :: hk h j, f :: vk h i) '(q, g)
  -> Sq '(r :: hk j k, g :: vk j l) '(s, e)
  -> Sq '(p `O` r, f) '(q `O` s, e)
Sq sqL === Sq sqR =
  ( let p = obj @p
        q = obj @q
        r = obj @r
        s = obj @s
        ec = mapCompanion @hk (obj @e)
        fc = mapCompanion @hk (obj @f)
        gc = mapCompanion @hk (obj @g)
    in (p `o` r) // (q `o` s) // Sq $
        associator fc q s
          . (sqL `o` s)
          . associatorInv p gc s
          . (p `o` sqR)
          . associator p r ec
  )
    \\\ sqL
    \\\ sqR

fromRight
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, DOb hk vk j, DOb hk vk k, Ob (f :: vk j k))
  => Sq '(I :: hk j j, I :: vk j j) '(Companion hk vk f, f)
fromRight = let comp = mapCompanion @hk @vk (obj @f) in Sq (compFromId `o` comp) \\ comp \\ iObj @hk @j \\ iObj @vk @j

toLeft
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, DOb hk vk j, DOb hk vk k, Ob (f :: vk j k))
  => Sq '(Companion hk vk f, f) '(I :: hk k k, I :: vk k k)
toLeft = let comp = mapCompanion @hk @vk (obj @f) in Sq (comp `o` compToId) \\ comp \\ iObj @hk @k \\ iObj @vk @k

toRight
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, DOb hk vk j, DOb hk vk k, Ob f)
  => Sq '(I :: hk j j, f) '(Conjoint hk vk f, I :: vk j j)
toRight = let f = obj @f in Sq (comConUnit @hk @vk f . rightUnitorWith (compToId @hk @vk) iObj) \\\ mapConjoint @hk @vk f \\ iObj @hk @j \\ iObj @vk @j

fromLeft
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, DOb hk vk j, DOb hk vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk vk f, I :: vk k k) '(I :: hk k k, f)
fromLeft = let f = obj @f in Sq (leftUnitorInvWith (compFromId @hk @vk) iObj . comConCounit @hk @vk f) \\\ mapConjoint @hk @vk f \\ iObj @hk @k \\ iObj @vk @k

class (Adjunction (Companion hk vk f) (Conjoint hk vk f)) => ComConAdjunction hk vk f
instance (Adjunction (Companion hk vk f) (Conjoint hk vk f)) => ComConAdjunction hk vk f

type Equipment :: forall {c}. CAT c -> CAT c -> Constraint
class (HasCompanions hk vk) => Equipment hk vk where
  type Conjoint hk vk (f :: vk j k) :: hk k j
  mapConjoint :: f ~> g -> Conjoint hk vk f ~> Conjoint hk vk g

  conjToId :: forall k. (Ob0 vk k) => Conjoint hk vk (I :: vk k k) ~> (I :: hk k k)
  conjToId = comConCounit iObj . rightUnitorInvWith compFromId (mapConjoint iObj)
  conjFromId :: forall k. (Ob0 vk k) => (I :: hk k k) ~> Conjoint hk vk (I :: vk k k)
  conjFromId = leftUnitorWith compToId (mapConjoint iObj) . comConUnit iObj

  conjToCompose :: Obj f -> Obj g -> Conjoint hk vk (f `O` g) ~> (Conjoint hk vk g `O` Conjoint hk vk f)
  conjToCompose f g =
    let
      fg = f `o` g
      comFG = mapCompanion @hk fg
      comF = mapCompanion @hk f
      comG = mapCompanion @hk g
      conFG = mapConjoint @hk fg
      conF = mapConjoint @hk f
      conG = mapConjoint @hk g
    in
      unStr
        ( ( ( str (conFG >> comFG >> SNil) SNil (comConCounit fg)
                . (singleton conFG `o` str (comF >> comG >> SNil) (comFG >> SNil) (compFromCompose f g))
            )
              `o` (singleton conG `o` singleton conF)
          )
            . ( singleton conFG
                  `o` ( (singleton comF `o` str SNil (comG >> conG >> SNil) (comConUnit g) `o` singleton conF)
                          . str SNil (comF >> conF >> SNil) (comConUnit f)
                      )
              )
        )
        \\\ f
        \\\ g

  conjFromCompose :: Obj f -> Obj g -> (Conjoint hk vk g `O` Conjoint hk vk f) ~> Conjoint hk vk (f `O` g)
  conjFromCompose f g =
    let
      fg = f `o` g
      comFG = mapCompanion @hk fg
      comF = mapCompanion @hk f
      comG = mapCompanion @hk g
      conFG = mapConjoint @hk fg
      conF = mapConjoint @hk f
      conG = mapConjoint @hk g
    in
      unStr
        ( ( ( str (conG >> comG >> SNil) SNil (comConCounit g)
                . (singleton conG `o` str (conF >> comF >> SNil) SNil (comConCounit f) `o` singleton comG)
            )
              `o` singleton conFG
          )
            . ( (singleton conG `o` singleton conF)
                  `o` ( (str (comFG >> SNil) (comF >> comG >> SNil) (compToCompose f g) `o` singleton conFG)
                          . str SNil (comFG >> conFG >> SNil) (comConUnit fg)
                      )
              )
        )
        \\\ f
        \\\ g

  comConUnit :: Obj f -> I ~> Companion hk vk f `O` Conjoint hk vk f
  default comConUnit
    :: forall f. (((Ob f) => ComConAdjunction hk vk f)) => Obj f -> I ~> Companion hk vk f `O` Conjoint hk vk f
  comConUnit f = unit @(Companion hk vk f) @(Conjoint hk vk f) \\\ f
  comConCounit :: Obj f -> Conjoint hk vk f `O` Companion hk vk f ~> I
  default comConCounit
    :: forall f. ((Ob f) => ComConAdjunction hk vk f) => Obj f -> Conjoint hk vk f `O` Companion hk vk f ~> I
  comConCounit f = counit @(Companion hk vk f) @(Conjoint hk vk f) \\\ f

companionFold
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Companion hk vk (Fold fs) ~> Fold (Companion (Path hk) (Path vk) fs)
companionFold SNil = compToId
companionFold (SCons f SNil) = mapCompanion f
companionFold (SCons f fs@SCons{}) = let cfs = mapCompanion @hk f `o` companionFold fs in (cfs . compToCompose f (fold fs)) \\\ cfs

foldCompanion
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Fold (Companion (Path hk) (Path vk) fs) ~> Companion hk vk (Fold fs)
foldCompanion SNil = compFromId
foldCompanion (SCons f SNil) = mapCompanion f
foldCompanion (SCons f fs@SCons{}) = let cfs = mapCompanion @hk f `o` foldCompanion fs in (compFromCompose f (fold fs) . cfs) \\\ cfs

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
        fgs = append fs gs
    in Str (mapCompanionSPath fgs) (cfs `append` cgs) $
        concatFold cfs cgs
          . (companionFold fs `o` companionFold gs)
          . compToCompose f g
          . mapCompanion (concatFold fs gs)
          . foldCompanion fgs
  compFromCompose (Str fs _ f) (Str gs _ g) =
    let cfs = mapCompanionSPath fs
        cgs = mapCompanionSPath gs
        fgs = append fs gs
    in Str (cfs `append` cgs) (mapCompanionSPath fgs) $
        companionFold fgs
          . mapCompanion (splitFold fs gs)
          . compFromCompose f g
          . (foldCompanion fs `o` foldCompanion gs)
          . splitFold cfs cgs

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
    in leftUnitorWith (comConCounit @(Path hk) fs) cgs
        . associatorInv cfs (tgt compN) cgs
        . (cfs `o` (compN `o` cgs))
        . rightUnitorInvWith (comConUnit gs) cfs

  comConUnit fs' = case asSPath fs' of
    SNil -> id
    SCons f sfs ->
      let fs = asObj sfs
          ls = mapCompanion @(Path hk) fs
          l = mapCompanion @hk f
          rs = mapConjoint @(Path hk) fs
          r = mapConjoint @hk f
          r' = singleton r
      in ((singleton l `o` (associator ls rs r' . (comConUnit @(Path hk) fs `o` r'))) . elimO . singleton (comConUnit f) . introI)
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
            . ( ( rightUnitorWith (elimI . singleton (comConCounit f) . introO @(Conjoint hk vk f) @(Companion hk vk f)) rs
                    . associator rs r' l'
                )
                  `o` ls
              )
            . associatorInv (rs `o` r') l' ls
         )
          \\\ rs
          \\\ l
          \\\ r

instance (Equipment hk vk) => HasCompanions (OPK hk) (COK vk) where
  type Companion (OPK hk) (COK vk) f = OP (Conjoint hk vk (UN CO f))
  mapCompanion (Co f) = Op (mapConjoint f)
  compToId = Op conjToId
  compFromId = Op conjFromId
  compToCompose (Co f) (Co g) = Op (conjToCompose f g)
  compFromCompose (Co f) (Co g) = Op (conjFromCompose f g)

instance (Equipment hk vk) => Equipment (OPK hk) (COK vk) where
  type Conjoint (OPK hk) (COK vk) f = OP (Companion hk vk (UN CO f))
  mapConjoint (Co f) = Op (mapCompanion f)
  conjToId = Op compToId
  conjFromId = Op compFromId
  conjToCompose (Co f) (Co g) = Op (compToCompose f g)
  conjFromCompose (Co f) (Co g) = Op (compFromCompose f g)
  comConUnit (Co f) = Op (comConUnit f)
  comConCounit (Co f) = Op (comConCounit f)
