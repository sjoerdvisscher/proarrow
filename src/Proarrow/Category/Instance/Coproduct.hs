module Proarrow.Category.Instance.Coproduct (COPRODUCT, L, R, (:++:), pattern InjL, pattern InjR) where

import Prelude (type (~))

import Proarrow.Core (CAT, CategoryOf (..))
import Proarrow.Profunctor.Initial (InitialProfunctor)
import Proarrow.Category.Instance.Collage (COLLAGE(..), Collage(..))

type COPRODUCT j k = COLLAGE (InitialProfunctor @j @k)

type (:++:) :: CAT j -> CAT k -> CAT (COPRODUCT j k)
type (:++:) c d = Collage :: CAT (COPRODUCT j k)

pattern InjL :: () => (a' ~ L a, b' ~ L b) => a ~> b -> ((~>) :++: (~>)) a' b'
pattern InjL f = InL f

pattern InjR :: () => (a' ~ R a, b' ~ R b) => a ~> b -> ((~>) :++: (~>)) a' b'
pattern InjR f = InR f

{-# COMPLETE InjL, InjR #-}
