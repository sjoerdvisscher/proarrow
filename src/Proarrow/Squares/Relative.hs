{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares.Relative where

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.Relative qualified as Rel
import Proarrow.Category.Bicategory.Strictified (Path (..), Strictified (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..), flipCompanion, flipConjointInv)
import Proarrow.Core (CategoryOf (..))

-- | The unit square for a @j@-relative monad @t@.
--
-- > A-----A
-- > |  /--j
-- > |  @  |
-- > |  \->t
-- > A-----A
unit
  :: forall {hk} {vk} {a} {e} {j :: hk e a} {t :: vk a e}
   . (Equipment hk vk, Rel.Monad j (Companion hk t), Ob0 vk a, Ob0 vk e, Ob t, Ob j)
  => Sq '(Nil, Nil :: Path vk a a) '(Companion hk t ::: j ::: Nil, Nil)
unit = Sq (St (Rel.unit @j @(Companion hk t)))

-- | The multiplication square for a @j@-relative monad @t@.
--
-- > E-----E
-- > t>-\  |
-- > j--@->t
-- > t>-/  |
-- > A-----A
mult
  :: forall {hk} {vk} {a} {e} {j :: hk e a} {t :: vk a e}
   . (Equipment hk vk, Rel.Monad j (Companion hk t), Ob0 vk a, Ob0 vk e, Ob t, Ob j)
  => Sq '(Companion hk t ::: j ::: Companion hk t ::: Nil, Nil :: Path vk e e) '(Companion hk t ::: Nil, Nil)
mult = Sq (St (Rel.mult @j @(Companion hk t)))

-- | @j@-relative adjunction
--
-- > A-----A
-- > |  /--j
-- > l<-@  |
-- > |  \->r
-- > C-----C
leftAdjunct
  :: forall {hk} {vk} {a} {c} {e} {j :: hk e a} {l :: vk a c} {r :: vk c e}
   . ( Equipment hk vk
     , Rel.Adjunction j (Companion hk l) (Companion hk r)
     , Ob0 vk a
     , Ob0 vk c
     , Ob0 vk e
     , Ob j
     , Ob l
     , Ob r
     )
  => Sq '(Conjoint hk l ::: Nil, Nil :: Path vk a a) '(Companion hk r ::: j ::: Nil, Nil :: Path vk c c)
leftAdjunct =
  withObConjoint @hk @vk @l
    ( Sq
        ( flipConjointInv @(l ::: Nil)
            (St (Rel.eta @j @(Companion hk l) @(Companion hk r)))
        )
    )

-- | @j@-relative adjunction, other direction
--
-- > A-----A
-- > j--\  |
-- > |  @<-l
-- > r->/  |
-- > C-----C
rightAdjunct
  :: forall {hk} {vk} {a} {c} {e} {j :: hk e a} {l :: vk a c} {r :: vk c e}
   . ( Equipment hk vk
     , Rel.Adjunction j (Companion hk l) (Companion hk r)
     , Ob0 vk a
     , Ob0 vk c
     , Ob0 vk e
     , Ob j
     , Ob l
     , Ob r
     )
  => Sq '(Companion hk r ::: j ::: Nil, Nil :: Path vk a a) '(Conjoint hk l ::: Nil, Nil :: Path vk c c)
rightAdjunct =
  withObConjoint @hk @vk @l
    ( Sq
        ( flipCompanion @(l ::: Nil)
            (St @(Companion hk r ::: j ::: Companion hk l ::: Nil) @Nil (Rel.epsilon @j @(Companion hk l) @(Companion hk r)))
        )
    )
