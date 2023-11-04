{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Monad where

import Data.Kind (Constraint)

import Proarrow.Category.Bicategory (Bicategory(..), Path(..), type (+++), MKKIND, obj1)
import Proarrow.Category.Bicategory.Prof (ProfK(..), Biprof(..), ProfList(..))
import Proarrow.Core (CategoryOf(..), Profunctor (..), Kind)
import Proarrow.Promonad (Promonad(..))
import Proarrow.Adjunction qualified as Pro
import Proarrow.Profunctor.Composition ((:.:)(..))


type Monad :: forall {kk :: MKKIND} {a :: Kind}. Path kk a a -> Constraint
class (Bicategory kk, BiOb kk a) => Monad (t :: Path kk a a) where
  return :: Nil ~> t
  join :: t +++ t ~> t

type Adjunction :: forall {kk :: MKKIND} {c :: Kind} {d :: Kind}. kk c d -> kk d c -> Constraint
class (Bicategory kk, BiOb kk c, BiOb kk d, Ob (l ::: Nil), Ob (r ::: Nil)) => Adjunction (l :: kk c d) (r :: kk d c) where
  unit :: Nil ~> r ::: l ::: Nil
  counit :: l ::: r ::: Nil ~> Nil

instance Adjunction l r => Monad (r ::: l ::: Nil) where
  return = unit
  join = obj1 `o` counit `o` obj1

instance Promonad p => Monad (PK p ::: Nil) where
  return = Biprof \(ProfNil f) -> ProfCons id (ProfNil f) \\ f
  join = Biprof \(ProfCons f (ProfCons g (ProfNil h))) -> ProfCons (g . f) (ProfNil h)

instance Pro.Adjunction l r => Adjunction (PK l) (PK r) where
  unit = Biprof \(ProfNil @a f) -> case Pro.unit @l @r @a \\ f of (r :.: l) -> ProfCons r (ProfCons l (ProfNil f))
  counit = Biprof \(ProfCons l (ProfCons r (ProfNil f))) -> ProfNil (f . Pro.counit @l @r (l :.: r))