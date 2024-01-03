{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Proarrow.Monad where

import Data.Kind (Type)
import Data.Function (($))

import Proarrow.Category.Bicategory (Bicategory(..), Path(..), type (+++), MKKIND, obj1, withAssoc, withUnital, appendObj)
import Proarrow.Category.Bicategory.Prof (ProfK(..), Biprof(..), ProfList(..), ProfConstraint)
import Proarrow.Core (CategoryOf(..), Profunctor (..), Kind, (//))
import Proarrow.Promonad (Promonad(..))
import Proarrow.Adjunction qualified as Pro
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Object (obj)

type RelMonad :: forall {kk :: MKKIND} {i :: Kind} {k :: Kind}. Path kk k i -> Path kk i k -> Type
data RelMonad j t where
  RelMonad :: (Bicategory kk, Ob0 kk i, Ob0 kk k) =>
    { return :: Nil ~> j +++ t
    , join :: (t +++ (j +++ t)) ~> t
    } -> RelMonad (j :: Path kk k i) (t :: Path kk i k)

type Monad = RelMonad Nil

idMonad :: (Bicategory kk, Ob0 kk a) => Monad (Nil :: Path kk a a)
idMonad = RelMonad { return = id, join = id }

type Adjunction :: forall {kk :: MKKIND} {c :: Kind} {d :: Kind}. Path kk c d -> Path kk d c -> Type
data Adjunction l r where
  Adjunction :: (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob l, Ob r) =>
    { unit :: Nil ~> r +++ l
    , counit :: l +++ r ~> Nil
    } -> Adjunction (l :: Path kk c d) (r :: Path kk d c)

idAdjunction :: (Bicategory kk, Ob0 kk a) => Adjunction (Nil :: Path kk a a) Nil
idAdjunction = Adjunction { unit = id, counit = id }

compAdjunction :: forall l1 r1 l2 r2. Adjunction l1 r1 -> Adjunction l2 r2 -> Adjunction (l2 +++ l1) (r1 +++ r2)
compAdjunction adj1@Adjunction{} adj2@Adjunction{} = appendObj @l2 @l1 $ appendObj @r1 @r2 $ Adjunction
  { unit = withAssoc @(r1 +++ r2) @l2 @l1 $ withAssoc @r1 @r2 @l2 $ withUnital @r1 $
      (obj @r1 `o` unit adj2 `o` obj @l1) . unit adj1
  , counit = withAssoc @(l2 +++ l1) @r1 @r2 $ withAssoc @l2 @l1 @r1 $ withUnital @l2 $
      counit adj2 . (obj @l2 `o` counit adj1 `o` obj @r2)
  }

adjMonad :: forall l r. Adjunction l r -> Monad (r +++ l)
adjMonad Adjunction{..} = RelMonad
  { return = unit
  , join = unit // withUnital @r $ withAssoc @r @l @r $ withAssoc @(r +++ l) @r @l $
      (obj @r `o` counit `o` obj @l)
  }

adjWrapMonad :: forall r l t. Adjunction (l ::: Nil) (r ::: Nil) -> Monad (t ::: Nil) -> Monad (r ::: t ::: l ::: Nil)
adjWrapMonad Adjunction{..} RelMonad{..} = RelMonad
  { return = (obj1 `o` return `o` obj1) . unit
  , join = obj1 @r `o` (join . (obj1 `o` counit `o` obj1)) `o` obj1 @l \\ return
  }

promonadMonad :: (Promonad p, ProfConstraint cl p) => Monad ((PK p ::: Nil) :: Path (ProfK cl) k k)
promonadMonad = RelMonad
  { return = Biprof \(ProfNil f) -> ProfCons id (ProfNil f) \\ f
  , join = Biprof \(ProfCons f (ProfCons g (ProfNil h))) -> ProfCons (g . f) (ProfNil h)
  }

proadjAdj :: (Pro.Adjunction l r, ProfConstraint cl l, ProfConstraint cl r) => Adjunction ((PK l ::: Nil) :: Path (ProfK cl) k k) (PK r ::: Nil)
proadjAdj = Adjunction
  { unit = Biprof \(ProfNil @a f) -> case Pro.unit \\ f of (r :.: l) -> ProfCons r (ProfCons l (ProfNil f))
  , counit = Biprof \(ProfCons l (ProfCons r (ProfNil f))) -> ProfNil (f . Pro.counit (l :.: r))
  }