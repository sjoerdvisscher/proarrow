{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Compiles the import incantation documented in "Proarrow"'s module header, using at least one
-- name from every section of its export list. Nothing else in the repo imports the front door, so
-- without this the documented line is never checked by a compiler.
module Examples.FrontDoor where

import Proarrow
import Prelude hiding (Functor, Monad, Monoid, fmap, id, map, mappend, mempty, return, (.))

-- categories and profunctors
frontId :: (CategoryOf k, Ob (a :: k)) => a ~> a
frontId = id

frontComp :: (CategoryOf k, Ob (a :: k), Ob b, Ob c) => b ~> c -> a ~> b -> a ~> c
frontComp = (.)

frontDimap :: (Profunctor p) => c ~> a -> b ~> d -> p a b -> p c d
frontDimap = dimap

-- objects
frontObj :: (CategoryOf k, Ob (a :: k)) => Obj a
frontObj = obj

-- functors
frontFmap :: forall f a b. (FunctorForRep f) => a ~> b -> f @ a ~> f @ b
frontFmap = fmap @f

-- promonads as effects
frontReturn :: forall m a. (Monad m, Ob a) => a ~> m % a
frontReturn = return @m

frontExtract :: forall w a. (Comonad w, Ob a) => w %% a ~> a
frontExtract = extract @w

-- The monoid section is usable from here alone. At a concrete category @Unit@ and @**@ reduce
-- (to @()@ and @(,)@ in Hask), so neither name has to be written and the monoidal vocabulary does
-- not have to be imported, even though 'Proarrow' exports none of it.
frontMempty :: () -> [Int]
frontMempty = mempty

frontMappend :: ([Int], [Int]) -> [Int]
frontMappend = mappend

-- universal properties and adjunctions
frontLeftAdjunct :: forall p a b. (Adjunction p, Ob a) => (p %% a ~> b) -> a ~> p % b
frontLeftAdjunct = leftAdjunct @p

-- optics
frontLens :: Lens' (Int, Char) Int
frontLens = lens fst (\((_, c), i) -> (i, c))

frontView :: (Int, Char) -> Int
frontView = view frontLens
