-- | Clocked state machines. Each step consumes one input and produces one output and the next
-- machine. Composition and tensor advance every component once per clock cycle.
--
-- >>> runSimulator (stateless not) [False, True]
-- [True,False]
-- >>> runSimulator (stateless (+ 1) . stateless (* 2)) [1 :: Int, 2]
-- [3,5]
module Proarrow.Category.Instance.Simulator
  ( SIMULATOR (..)
  , Simulator (..)
  , stateless
  , step
  , runSimulator
  ) where

import Data.Kind (Type)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..))

type data SIMULATOR = Sim Type

-- | A machine and its current state, represented by its next step.
type Simulator :: CAT SIMULATOR
data Simulator a b where
  Simulator :: (a -> (b, Simulator (Sim a) (Sim b))) -> Simulator (Sim a) (Sim b)

-- | Apply a function independently in every clock cycle.
stateless :: (a -> b) -> Simulator (Sim a) (Sim b)
stateless f = machine
  where
    machine = Simulator \x -> (f x, machine)

instance CategoryOf SIMULATOR where
  type (~>) = Simulator
  type Ob a = Is Sim a
instance Profunctor Simulator where
  dimap = dimapDefault
  r \\ Simulator{} = r
instance Promonad Simulator where
  id = stateless \x -> x
  Simulator f . Simulator g = Simulator \x ->
    let (y, g') = g x
        (z, f') = f y
    in (z, f' . g')
instance MonoidalProfunctor Simulator where
  one = id
  Simulator f ** Simulator g = Simulator \(x, y) ->
    let (x', f') = f x
        (y', g') = g y
    in ((x', y'), f' ** g')
instance Monoidal SIMULATOR where
  type Unit = Sim ()
  type a ** b = Sim (UN Sim a, UN Sim b)
  withOb2 r = r
  leftUnitor = stateless \((), x) -> x
  leftUnitorInv = stateless ((),)
  rightUnitor = stateless \(x, ()) -> x
  rightUnitorInv = stateless (,())
  associator = stateless \((x, y), z) -> (x, (y, z))
  associatorInv = stateless \(x, (y, z)) -> ((x, y), z)
instance SymMonoidal SIMULATOR where
  swap = stateless \(x, y) -> (y, x)
instance (Ob a) => Comonoid (a :: SIMULATOR) where
  counit = stateless (const ())
  comult = stateless \x -> (x, x)
instance (Ob a) => CocommutativeComonoid (a :: SIMULATOR)
instance CopyDiscard SIMULATOR

-- | Observe the current output and advance one clock cycle.
step :: Simulator (Sim a) (Sim b) -> a -> (b, Simulator (Sim a) (Sim b))
step (Simulator run) = run

-- | Run a sequence of inputs, starting from the machine's current state.
runSimulator :: Simulator (Sim a) (Sim b) -> [a] -> [b]
runSimulator _ [] = []
runSimulator machine (x : xs) =
  let (y, next) = step machine x
  in y : runSimulator next xs
