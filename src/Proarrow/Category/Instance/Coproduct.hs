{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Instance.Coproduct (COPRODUCT, COLLAGE(..), (:++:), pattern InjL, pattern InjR) where

import Prelude (type (~))

import Proarrow.Core (CAT, CategoryOf (..))
import Proarrow.Profunctor.Initial (InitialProfunctor)
import Proarrow.Category.Instance.Collage (COLLAGE(..), Collage(..))
import Proarrow.Category.Dagger (DaggerProfunctor (..), Dagger)

type COPRODUCT j k = COLLAGE (InitialProfunctor @j @k)

type (:++:) :: CAT j -> CAT k -> CAT (COPRODUCT j k)
type (:++:) c d = Collage :: CAT (COPRODUCT j k)

pattern InjL :: () => (a' ~ L a, b' ~ L b) => a ~> b -> ((~>) :++: (~>)) a' b'
pattern InjL f = InL f

pattern InjR :: () => (a' ~ R a, b' ~ R b) => a ~> b -> ((~>) :++: (~>)) a' b'
pattern InjR f = InR f

{-# COMPLETE InjL, InjR #-}

instance (Dagger j, Dagger k) => DaggerProfunctor ((~>) :++: (~>) :: CAT (COPRODUCT j k)) where
  dagger = \case
    InL f -> InL (dagger f)
    InR f -> InR (dagger f)
