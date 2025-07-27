{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares.Relative where

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.Relative qualified as Rel
import Proarrow.Category.Bicategory.Strictified (Path (..), SPath (..), Strictified (..), singleton)
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..), flipCompanion, flipConjointInv)
import Proarrow.Core (CategoryOf (..), obj)

-- | The unit square for a @j@-relative monad @t@.
--
-- > A-----A
-- > |  /-<j
-- > |  @  |
-- > |  \->t
-- > A-----A
unit
  :: forall {hk} {vk} {a} {e} {j :: vk a e} {t :: vk a e}
   . (Equipment hk vk, Rel.Monad (Conjoint hk j) (Companion hk t), Ob0 vk a, Ob0 vk e, Ob t, Ob j)
  => Sq '(Nil, Nil :: Path vk a a) '(Companion hk t ::: Conjoint hk j ::: Nil, Nil)
unit =
  let jc = mapConjoint @hk (obj @j); tc = mapCompanion @hk (obj @t)
  in Sq (Str SNil (SCons tc (SCons jc SNil)) (Rel.unit @(Conjoint hk j) @(Companion hk t)))

-- | The multiplication square for a @j@-relative monad @t@.
--
-- > E-----E
-- > t>-\  |
-- > j<-@->t
-- > t>-/  |
-- > A-----A
mult
  :: forall {hk} {vk} {a} {e} {j :: vk a e} {t :: vk a e}
   . (Equipment hk vk, Rel.Monad (Conjoint hk j) (Companion hk t), Ob0 vk a, Ob0 vk e, Ob t, Ob j)
  => Sq '(Companion hk t ::: Conjoint hk j ::: Companion hk t ::: Nil, Nil :: Path vk e e) '(Companion hk t ::: Nil, Nil)
mult =
  let jc = mapConjoint @hk (obj @j); tc = mapCompanion @hk (obj @t)
  in Sq (Str (SCons tc (SCons jc (SCons tc SNil))) (SCons tc SNil) (Rel.mult @(Conjoint hk j) @(Companion hk t)))

-- | @j@-relative adjunction
--
-- > A-----A
-- > |  /-<j
-- > l<-@  |
-- > |  \->r
-- > C-----C
leftAdjunct
  :: forall {hk} {vk} {a} {c} {e} {j :: vk a e} {l :: vk a c} {r :: vk c e}
   . ( Equipment hk vk
     , Rel.Adjunction (Conjoint hk j) (Companion hk l) (Companion hk r)
     , Ob0 vk a
     , Ob0 vk c
     , Ob0 vk e
     , Ob j
     , Ob l
     , Ob r
     )
  => Sq '(Conjoint hk l ::: Nil, Nil :: Path vk a a) '(Companion hk r ::: Conjoint hk j ::: Nil, Nil :: Path vk c c)
leftAdjunct =
  let l = obj @l; jc = mapConjoint @hk (obj @j); lc = mapCompanion @hk l; rc = mapCompanion @hk (obj @r)
  in Sq
       ( flipConjointInv
           (singleton l)
           (Str SNil (SCons lc (SCons rc (SCons jc SNil))) (Rel.eta @(Conjoint hk j) @(Companion hk l) @(Companion hk r)))
       )
       \\\ mapConjoint @hk l

-- | @j@-relative adjunction, other direction
--
-- > A-----A
-- > j<-\  |
-- > |  @<-l
-- > r->/  |
-- > C-----C
rightAdjunct
  :: forall {hk} {vk} {a} {c} {e} {j :: vk a e} {l :: vk a c} {r :: vk c e}
   . ( Equipment hk vk
     , Rel.Adjunction (Conjoint hk j) (Companion hk l) (Companion hk r)
     , Ob0 vk a
     , Ob0 vk c
     , Ob0 vk e
     , Ob j
     , Ob l
     , Ob r
     )
  => Sq '(Companion hk r ::: Conjoint hk j ::: Nil, Nil :: Path vk a a) '(Conjoint hk l ::: Nil, Nil :: Path vk c c)
rightAdjunct =
  let l = obj @l; jc = mapConjoint @hk (obj @j); lc = mapCompanion @hk l; rc = mapCompanion @hk (obj @r)
  in Sq
       ( flipCompanion
           (singleton l)
           (Str (SCons rc (SCons jc (SCons lc SNil))) SNil (Rel.epsilon @(Conjoint hk j) @(Companion hk l) @(Companion hk r)))
       )
       \\\ mapConjoint @hk l