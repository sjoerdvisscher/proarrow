{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Squares.Relative where

import Proarrow.Category.Bicategory.Relative qualified as Rel
import Proarrow.Category.Bicategory.Strictified (Path (..), SPath (..), Strictified (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq (..))
import Proarrow.Core (CategoryOf (..), obj)
import Proarrow.Category.Bicategory (Bicategory(..))

-- | The unit square for a @j@-relative monad @t@.
--
-- > A-----A
-- > |  /-<j
-- > |  @  |
-- > |  \->t
-- > A-----A
unit :: forall {hk} {vk} {a} {e} {j :: vk a e} {t :: vk a e}
     . (Equipment hk vk, Rel.Monad (Conjoint hk j) (Companion hk t), Ob0 vk a, Ob0 vk e, Ob t, Ob j)
     => Sq '(Nil, Nil :: Path vk a a) '(Companion hk t ::: Conjoint hk j ::: Nil, Nil)
unit = let jc = mapConjoint @hk (obj @j); tc = mapCompanion @hk (obj @t)
  in Sq (Str SNil (SCons tc (SCons jc SNil)) (Rel.unit @(Conjoint hk j) @(Companion hk t)))

-- | The multiplication square for a @j@-relative monad @t@.
--
-- > E-----E
-- > t>-\  |
-- > j<-@->t
-- > t>-/  |
-- > A-----A
mult :: forall {hk} {vk} {a} {e} {j :: vk a e} {t :: vk a e}
     . (Equipment hk vk, Rel.Monad (Conjoint hk j) (Companion hk t), Ob0 vk a, Ob0 vk e, Ob t, Ob j)
     => Sq '(Companion hk t ::: Conjoint hk j ::: Companion hk t ::: Nil, Nil :: Path vk e e) '(Companion hk t ::: Nil, Nil)
mult = let jc = mapConjoint @hk (obj @j); tc = mapCompanion @hk (obj @t)
  in Sq (Str (SCons tc (SCons jc (SCons tc SNil))) (SCons tc SNil) (Rel.mult @(Conjoint hk j) @(Companion hk t)))