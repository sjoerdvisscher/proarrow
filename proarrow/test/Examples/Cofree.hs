{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | A worked instance of 'HasCofree', checked by the typechecker only. The cofree @Test@ object
-- on a Hask type is that type paired with the @Int@ the class produces, and that makes the
-- coKleisli category of the env comonad a 'Promonad'. There is nothing to assert at runtime, so
-- this module exports no 'Test.Tasty.TestTree'. Compiling it is the test, as in "Examples.Free".
module Examples.Cofree where

import Prelude (Int, fst, snd)

import Proarrow.Core (Promonad (..))
import Proarrow.Profunctor.Cofree (HasCofree (..), cofreeComp)
import Proarrow.Profunctor.Instance.Costar (Costar, pattern Costar)

class Test a where
  test :: a -> Int

instance HasCofree Test where
  type Cofree Test a = (Int, a)
  lower = snd
  unfoldMap f a = (test a, f a)

instance Test (Int, a) where
  test = fst

instance Promonad (Costar ((,) Int)) where
  id = Costar (lower @Test)
  Costar l . Costar r = Costar (cofreeComp @Test l r)
