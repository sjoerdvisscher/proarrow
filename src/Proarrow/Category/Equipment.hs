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
  , iObj
  , leftUnitorInvWith
  , leftUnitorWith
  , rightUnitorInvWith
  , rightUnitorWith
  , (==)
  , (||)
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

  withObCompanion :: forall {j} {k} f r. (Ob (f :: vk j k)) => ((Ob (Companion hk f)) => r) -> r

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
  {-# MINIMAL mapConjoint, withObConjoint #-}
  type Conjoint hk (f :: vk j k) :: hk k j
  mapConjoint :: forall {j} {k} (f :: vk j k) g. f ~> g -> Conjoint hk g ~> Conjoint hk f

  withObConjoint :: forall {j} {k} f r. (Ob (f :: vk j k)) => ((Ob (Conjoint hk f)) => r) -> r

  conjToId :: forall k. (Ob0 vk k) => Conjoint hk (I :: vk k k) ~> (I :: hk k k)
  conjToId = comConCounit iObj . leftUnitorInvWith compFromId (mapConjoint iObj)
  conjFromId :: forall k. (Ob0 vk k) => (I :: hk k k) ~> Conjoint hk (I :: vk k k)
  conjFromId = rightUnitorWith compToId (mapConjoint iObj) . comConUnit iObj

  conjToCompose
    :: forall {j} {k} (f :: vk j k) g. Obj f -> Obj g -> Conjoint hk (f `O` g) ~> (Conjoint hk g `O` Conjoint hk f)
  conjToCompose f g =
    ( let
        fg = f `o` g
        comF = mapCompanion @hk f
        comG = mapCompanion @hk g
        conFG = mapConjoint @hk fg
        conF = mapConjoint @hk f
        conG = mapConjoint @hk g
      in
        (rightUnitorWith (comConCounit fg . (compFromCompose f g `o` conFG)) (conG `o` conF))
          . associator' (conG `o` conF) (comF `o` comG) conFG
          . (associator' (conG `o` conF) comF comG `o` conFG)
          . ((associatorInv' conG conF comF `o` comG) `o` conFG)
          . (leftUnitorInvWith ((rightUnitorInvWith (comConUnit f) conG `o` comG) . comConUnit g) conFG)
    )
      \\\ f
      \\\ g

  conjFromCompose
    :: forall {j} {k} (f :: vk j k) g. Obj f -> Obj g -> (Conjoint hk g `O` Conjoint hk f) ~> Conjoint hk (f `O` g)
  conjFromCompose f g =
    ( let
        fg = f `o` g
        comF = mapCompanion @hk f
        comG = mapCompanion @hk g
        conFG = mapConjoint @hk fg
        conF = mapConjoint @hk f
        conG = mapConjoint @hk g
      in
        (rightUnitorWith (comConCounit f . (rightUnitorWith (comConCounit g) comF `o` conF)) conFG)
          . (conFG `o` ((associator' comF comG conG `o` conF) . associatorInv' (comF `o` comG) conG conF))
          . associator' conFG (comF `o` comG) (conG `o` conF)
          . (leftUnitorInvWith ((conFG `o` compToCompose f g) . comConUnit fg) (conG `o` conF))
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
object = hArr id

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
  in Sq (leftUnitorInv . n' . rightUnitor) \\ n \\ n'

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
    in withOb2 @vk @g @e $
        withOb2 @vk @f @d $
          dc //
            ec //
              fc //
                gc //
                  Sq $
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
        s = obj @s
        ec = mapCompanion @hk (obj @e)
        fc = mapCompanion @hk (obj @f)
        gc = mapCompanion @hk (obj @g)
    in withOb2 @hk @r @p $
        withOb2 @hk @s @q $
          ec //
            fc //
              gc //
                Sq $
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
toRight = let comp = mapCompanion @hk @vk (obj @f) in Sq (comp `o` compFromId) \\ comp

-- > k-----k
-- > |     |
-- > f>-\  |
-- > |  v  |
-- > j--f--k
fromLeft
  :: forall {hk} {vk} {j} {k} f
   . (HasCompanions hk vk, Ob' (f :: vk j k))
  => Sq '(Companion hk f, I :: vk k k) '(I :: hk k k, f)
fromLeft = let comp = mapCompanion @hk @vk (obj @f) in Sq (compToId `o` comp) \\ comp

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
  in Sq (comConUnit @hk @vk f . leftUnitorWith (compToId @hk @vk) id)
      \\\ mapConjoint @hk @vk f

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
  in Sq (rightUnitorInvWith (compFromId @hk @vk) id . comConCounit @hk @vk f)
      \\\ mapConjoint @hk @vk f

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
-- The kind of a retro square @'(q, g) '(p, f)@.
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
