{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Category.Double where

import Data.Kind (Constraint)
import Prelude (($), type (~))

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
-- > h--f--i
-- > |  v  |
-- > p--@--q
-- > |  v  |
-- > j--g--k
type SQ' (hk :: CAT c) (vk :: CAT c) h i j k = PRO (hk h j, vk h i) (hk i k, vk j k)

type SQ (hk :: CAT c) (vk :: CAT c) = forall {h} {i} {j} {k}. SQ' hk vk h i j k

-- | A double category with companions.
type HasCompanions :: forall {c}. CAT c -> CAT c -> Constraint
class (Bicategory hk, Bicategory vk) => HasCompanions hk vk | hk -> vk where
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
object = hArr id

-- | Make a square from a horizontal arrow
hArr
  :: forall {hk} {vk} {j} {k} (p :: hk j k) q
   . (HasCompanions hk vk, DOb hk vk j, DOb hk vk k)
  => p ~> q
  -> Sq '(p, I :: vk j j) '(q, I :: vk k k)
hArr n =
  Sq (leftUnitorInvWith (compFromId @hk @vk) (tgt n) . n . rightUnitorWith (compToId @hk @vk) (src n))
    \\ n

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
vArr n = let n' = mapCompanion @hk @vk n in Sq (rightUnitorInv (tgt n') . n' . leftUnitor (src n')) \\ n

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
   . (HasCompanions hk vk, DOb hk vk j, DOb hk vk k, Ob (f :: vk j k), Companion hk vk (I :: vk j j) ~ I)
  => Sq '(I :: hk j j, I :: vk j j) '(Companion hk vk f, f)
fromRight = let comp = mapCompanion @hk @vk (obj @f) in Sq (obj @I `o` comp) \\ comp

toLeft
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, DOb hk vk j, DOb hk vk k, Ob (f :: vk j k), Companion hk vk (I :: vk k k) ~ I)
  => Sq '(Companion hk vk f, f) '(I, I)
toLeft = let comp = mapCompanion @hk @vk (obj @f) in Sq (comp `o` obj @I) \\ comp

toRight
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, DOb hk vk j, DOb hk vk k, Ob f)
  => Sq '(I, f) '(Conjoint hk vk f, I)
toRight = let f = obj @f in Sq (comConUnit @hk @vk f . rightUnitorWith (compToId @hk @vk) id) \\\ mapConjoint @hk @vk f

fromLeft
  :: forall {hk} {vk} {j} {k} (f :: vk j k)
   . (Equipment hk vk, DOb hk vk j, DOb hk vk k, Ob (f :: vk j k))
  => Sq '(Conjoint hk vk f, I) '(I, f)
fromLeft = let f = obj @f in Sq (leftUnitorInvWith (compFromId @hk @vk) id . comConCounit @hk @vk f) \\\ mapConjoint @hk @vk f

type Equipment :: forall {c}. CAT c -> CAT c -> Constraint
class (HasCompanions hk vk) => Equipment hk vk where
  type Conjoint hk vk (f :: vk j k) :: hk k j
  mapConjoint :: f ~> g -> Conjoint hk vk f ~> Conjoint hk vk g

  conjToId :: forall k. (Ob0 vk k) => Conjoint hk vk (I :: vk k k) ~> (I :: hk k k)
  conjToId =
    let i = obj @(I :: vk k k); conI = mapConjoint @hk @vk i
    in (comConCounit @hk @vk i . rightUnitorInvWith (compFromId @hk @vk) conI) \\\ conI
  conjFromId :: forall k. (Ob0 vk k) => (I :: hk k k) ~> Conjoint hk vk (I :: vk k k)
  conjFromId =
    let i = obj @(I :: vk k k); conI = mapConjoint @hk @vk i
    in (leftUnitorWith (compToId @hk @vk) conI . comConUnit @hk @vk i) \\\ conI

  conjToCompose :: Obj f -> Obj g -> Conjoint hk vk (f `O` g) ~> (Conjoint hk vk g `O` Conjoint hk vk f)
  conjFromCompose :: Obj f -> Obj g -> (Conjoint hk vk g `O` Conjoint hk vk f) ~> Conjoint hk vk (f `O` g)

  comConUnit :: Obj f -> I ~> Companion hk vk f `O` Conjoint hk vk f
  default comConUnit
    :: forall f
     . (Ob f, Adjunction (Companion hk vk f) (Conjoint hk vk f))
    => Obj f
    -> I ~> Companion hk vk f `O` Conjoint hk vk f
  comConUnit _ = unit @(Companion hk vk f) @(Conjoint hk vk f)
  comConCounit :: Obj f -> Conjoint hk vk f `O` Companion hk vk f ~> I
  default comConCounit
    :: forall f. (Adjunction (Companion hk vk f) (Conjoint hk vk f)) => Obj f -> Conjoint hk vk f `O` Companion hk vk f ~> I
  comConCounit _ = counit @(Companion hk vk f) @(Conjoint hk vk f)

-- instance
--   (Double hk vk, DOb hk vk h, DOb hk vk i, DOb hk vk j, DOb hk vk k)
--   => Profunctor (Sq (Path hk) (Path vk) :: PRO (Path hk h j, Path vk h i) (Path hk i k, Path vk j k))
--   where
--   dimap (Str p :**: Str f) (Str q :**: Str g) (PathSq sq) = PathSq (dimap (p :**: f) (q :**: g) sq)
--   r \\ PathSq sq = r \\ sq

-- instance (Double hk vk) => Double (Path hk) (Path vk) where
--   data Sq (Path hk) (Path vk) psfs qsgs where
--     PathSq
--       :: forall {hk} {vk} ps qs fs gs
--        . (IsPath ps, IsPath qs, IsPath fs, IsPath gs)
--       => {unPathSq :: Sq '(Fold ps, Fold fs) '(Fold qs, Fold gs)}
--       -> Sq (Path hk) (Path vk) '(ps, fs) '(qs, gs)
--   hArr (Str p) = PathSq (hArr p)
--   vArr (Str f) = PathSq (vArr f)
--   PathSq @_ @_ @fs @gs f `hComp` PathSq @_ @_ @hs @is g =
--     ( appendObj @fs @hs $
--         appendObj @gs @is $
--           PathSq $
--             dimap (id :**: splitFold @fs @hs) (id :**: concatFold @gs @is) (f `hComp` g)
--     )
--       \\\\ f
--       \\\\ g

--   PathSq @ps @qs f `vComp` PathSq @rs @ss g =
--     ( appendObj @ps @rs $
--         appendObj @qs @ss $
--           PathSq $
--             dimap (splitFold @ps @rs :**: id) (concatFold @qs @ss :**: id) (f `vComp` g)
--     )
--       \\\\ f
--       \\\\ g
--   r \\\\ PathSq f = r \\\\ f

companionFold
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Companion hk vk (Fold fs) ~> Fold (Companion (Path hk) (Path vk) fs)
companionFold SNil = compToId @hk @vk
companionFold (SCons f SNil) = mapCompanion @hk @vk f
companionFold (SCons f fs@SCons{}) = let cfs = mapCompanion @hk @vk f `o` companionFold fs in (cfs . compToCompose @hk @vk f (fold fs)) \\\ cfs

foldCompanion
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (HasCompanions hk vk)
  => SPath fs
  -> Fold (Companion (Path hk) (Path vk) fs) ~> Companion hk vk (Fold fs)
foldCompanion SNil = compFromId @hk @vk
foldCompanion (SCons f SNil) = mapCompanion @hk @vk f
foldCompanion (SCons f fs@SCons{}) = let cfs = mapCompanion @hk @vk f `o` foldCompanion fs in (compFromCompose @hk @vk f (fold fs) . cfs) \\\ cfs

instance (HasCompanions hk vk) => HasCompanions (Path hk) (Path vk) where
  type Companion (Path hk) (Path vk) Nil = Nil
  type Companion (Path hk) (Path vk) (p ::: ps) = Companion hk vk p ::: Companion (Path hk) (Path vk) ps

  mapCompanion (Str @fs @gs n) = Str $ companionFold (singPath @fs) . mapCompanion @hk @vk n . foldCompanion (singPath @gs)

  compToId = Str id
  compFromId = Str id
  compToCompose (Str @fs _) (Str @gs _) = Str $ go (singPath @fs)
    where
      go
        :: forall fs
         . SPath fs
        -> Fold (Companion (Path hk) (Path vk) (fs +++ gs))
          ~> Fold
              ( Companion (Path hk) (Path vk) fs
                  +++ Companion (Path hk) (Path vk) gs
              )
      go SNil = id
      go (SCons f SNil) = _

conjointFold
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (Equipment hk vk)
  => SPath fs
  -> Conjoint hk vk (Fold fs) ~> Fold (Conjoint (Path hk) (Path vk) fs)
conjointFold = _

foldConjoint
  :: forall {hk} {vk} {j} {k} (fs :: Path vk j k)
   . (Equipment hk vk)
  => SPath fs
  -> Fold (Conjoint (Path hk) (Path vk) fs) ~> Conjoint hk vk (Fold fs)
foldConjoint = _

instance (Equipment hk vk) => Equipment (Path hk) (Path vk) where
  type Conjoint (Path hk) (Path vk) Nil = Nil
  type Conjoint (Path hk) (Path vk) (p ::: ps) = Conjoint (Path hk) (Path vk) ps +++ (Conjoint hk vk p ::: Nil)

  mapConjoint (Str @fs @gs n) = Str $ conjointFold (singPath @gs) . mapConjoint @hk @vk n . foldConjoint (singPath @fs)

  comConUnit fs' = case asSPath fs' of
    SNil -> id \\\ mapConjoint @(Path hk) fs'
    SCons f sfs ->
      let fs = asObj sfs
          ls = mapCompanion @(Path hk) fs
          l = mapCompanion @hk f
          rs = mapConjoint @(Path hk) fs
          r = mapConjoint @hk f
          r' = singleton r
      in ( (singleton l `o` (associator ls rs r' . (comConUnit @(Path hk) fs `o` r'))) . elimO . singleton (comConUnit f) . introI
         )
          \\\ l
          \\\ r

  comConCounit fs' = case asSPath fs' of
    SNil -> id \\\ mapConjoint @(Path hk) fs'
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