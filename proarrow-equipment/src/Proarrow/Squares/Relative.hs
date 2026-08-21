{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Squares.Relative where

import Proarrow.Category.Bicategory (flipLeftAdjoint, flipRightAdjointInv)
import Proarrow.Category.Bicategory.Relative qualified as Rel
import Proarrow.Category.Bicategory.Strictified (Path (..), Strictified (..))
import Proarrow.Category.Equipment (Equipment (..), IsTight, TightPair)
import Proarrow.Squares (Sq, Sq' (..))

-- | The unit square for a @j@-relative monad @t@.
--
-- > A-----A
-- > |  /--j
-- > |  @  |
-- > |  \->t
-- > A-----A
unit
  :: forall {kk} {a} {e} {j :: kk e a} {t :: kk a e}
   . (Equipment kk, Rel.Monad j t, IsTight t)
  => Sq Nil (t ::: j ::: Nil) Nil Nil
unit = Sq (St (Rel.unit @j @t))

-- | The multiplication square for a @j@-relative monad @t@.
--
-- > A-------A
-- > j--\ /-<t
-- > |   @   |
-- > t>-/ \->t
-- > A-------A
mult
  :: forall {kk} {a} {e} {j :: kk e a} {t :: kk a e} t'
   . (Equipment kk, Rel.Monad j t, TightPair t t')
  => Sq (t ::: j ::: Nil) (t ::: t' ::: Nil) Nil Nil
mult = Sq (flipLeftAdjoint @(t ::: Nil) (St @(t ::: j ::: t ::: Nil) @(t ::: Nil) (Rel.mult @j @t)))

-- | @j@-relative adjunction
--
-- > A-----A
-- > |  /--j
-- > l<-@  |
-- > |  \->r
-- > C-----C
leftAdjunct
  :: forall {kk} {a} {c} {e} {j :: kk e a} {l :: kk a c} {l' :: kk c a} {r :: kk c e}
   . (Equipment kk, Rel.Adjunction j l r, IsTight r, TightPair l l')
  => Sq (l' ::: Nil) (r ::: j ::: Nil) Nil Nil
leftAdjunct = Sq (flipRightAdjointInv @(l ::: Nil) (St @Nil @(l ::: r ::: j ::: Nil) (Rel.eta @j @l @r)))

-- | @j@-relative adjunction, other direction
--
-- > A-----A
-- > j--\  |
-- > |  @<-l
-- > r->/  |
-- > C-----C
rightAdjunct
  :: forall {kk} {a} {c} {e} {j :: kk e a} {l :: kk a c} {l' :: kk c a} {r :: kk c e}
   . (Equipment kk, Rel.Adjunction j l r, IsTight r, TightPair l l')
  => Sq (r ::: j ::: Nil) (l' ::: Nil) Nil Nil
rightAdjunct = Sq (flipLeftAdjoint @(l ::: Nil) (St @(r ::: j ::: l ::: Nil) @Nil (Rel.epsilon @j @l @r)))
