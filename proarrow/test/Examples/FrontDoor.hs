{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Compiles the import incantation documented in "Proarrow"'s module header, using one name from
-- each section of the export list. Nothing else in the repo imports the front door, so without this
-- the documented line is never checked by a compiler.
module Examples.FrontDoor where

import Proarrow
import Prelude hiding (Functor, Monad, Monoid, fmap, id, map, mappend, mempty, return, (.))

-- the core vocabulary
frontId :: (CategoryOf k, Ob (a :: k)) => a ~> a
frontId = id

frontComp :: (CategoryOf k, Ob (a :: k), Ob b, Ob c) => b ~> c -> a ~> b -> a ~> c
frontComp = (.)

frontDimap :: (Profunctor p) => c ~> a -> b ~> d -> p a b -> p c d
frontDimap = dimap

frontFmap :: forall f a b. (FunctorForRep f) => a ~> b -> f @ a ~> f @ b
frontFmap = fmap @f

-- The monoid section is usable from here alone: at a concrete category @Unit@ and @**@ reduce --
-- to @()@ and @(,)@ in Hask -- so neither name has to be written and the monoidal vocabulary does
-- not have to be imported, even though 'Proarrow' exports none of it.
frontMempty :: () -> [Int]
frontMempty = mempty

frontMappend :: ([Int], [Int]) -> [Int]
frontMappend = mappend
