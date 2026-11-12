{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}

-- | Finite deterministic open games. A wire @'G' x s@ carries observations @x@
-- forward and coutilities @s@ backward. Sequential composition is categorical
-- composition; the symmetric monoidal tensor plays games in parallel.
--
-- This specialises "Proarrow.Category.Instance.OpenGame" to Haskell types.
-- Play is a 'MonoidalLens' with a shared forward/backward residual.
-- Build it with 'monLens', or lift a cartesian lens with 'fromLens'.
--
-- Evaluation checks unilateral deviations at the observation reached in the
-- supplied context. It does not impose subgame perfection at unreached nodes.
--
-- Model deterministic games with ordinary Haskell and the qualified @do@
-- notation of "Proarrow.Tools.SMC", without Template Haskell or a quasiquoter.
-- A term of type @'F' ('G' x s)@ carries an observation @x@ forward and
-- coutility @s@ backward. Bind decisions, then supply their returns together
-- with 'payoffs' or 'finish', once all actions are in scope. The game wires
-- the returns backward automatically; no recursive @do@ or trace is required.
--
-- For example, a two-player simultaneous game has the form
--
-- @
-- game = toSMC \@I \\() -> SMC.do
--   a <- choose "Alice" [Cooperate, Defect] -< ()
--   b <- choose "Bob" [Cooperate, Defect] -< ()
--   finish (\\(a, b) -> (alicePayoff a b, bobPayoff a b)) -< (a, b)
-- @
--
-- Use @OverloadedLists@ and @QualifiedDo@, import @toSMC@, 'I' (through @SYN (..)@) and @(-<)@
-- from "Proarrow.Tools.SMC", and import that module qualified as @SMC@.
-- The payoff lambda receives ordinary Haskell values, so it can freely reuse
-- them. At the SMC level, use 'observe' when a later decision observes an
-- earlier action while that action must also remain available for payoffs.
module Examples.OpenGames.Deterministic
  ( GAME
  , G
  , Observation
  , Coutility
  , Context
  , pattern Context
  , Payoff
  , Diagnostic (..)
  , isEquilibrium
  , OpenGame
  , pattern OpenGame
  , profiles
  , play
  , evaluate
  , Game
  , pattern Game
  , Strategy
  , playStrategy
  , evaluateStrategy
  , runStrategy
  , outputs
  , strategies
  , equilibria
  , withGame
  , fromMonoidalLens
  , fromLens
  , fromFunctions
  , andThen
  , parallel
  , reindex
  , decision

    -- * SMC notation
  , choose
  , decide
  , payoffs
  , finish
  , observe
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe)
import Prelude hiding (id, (**), (.))
import Prelude qualified as P

import Proarrow.Category.Instance.OpenGame
  ( Diagnostic (..)
  , Payoff
  , andThen
  , equilibria
  , evaluateStrategy
  , fromMonoidalLens
  , isEquilibrium
  , parallel
  , playStrategy
  , reindex
  , strategies
  , withGame
  )
import Proarrow.Category.Instance.OpenGame qualified as Generic
import Proarrow.Category.Monoidal.Strictified (Fold)
import Proarrow.Core (CAT, CategoryOf (..))
import Proarrow.Optic.Lens (Lens, lens, withLens)
import Proarrow.Optic.MonoidalLens (MonoidalLens, monLens)
import Proarrow.Tools.SMC (SYN (..), Term, lift, recast)

type GAME = Generic.GAME Type

type G :: Type -> Type -> GAME
type G x s = Generic.G x s

type Observation :: GAME -> Type
type Observation a = Generic.Observation a

type Coutility :: GAME -> Type
type Coutility a = Generic.Coutility a

type Context :: GAME -> GAME -> Type
type Context = Generic.Context @Type

type OpenGame :: [Type] -> GAME -> GAME -> Type
type OpenGame = Generic.OpenGame @Type

pattern OpenGame
  :: forall ss a b
   . ()
  => (Ob ss, Ob a, Ob b)
  => [Fold ss]
  -> (Fold ss -> MonoidalLens (Generic.Observation a) (Generic.Coutility a) (Generic.Observation b) (Generic.Coutility b))
  -> (Fold ss -> Context a b -> [Diagnostic])
  -> OpenGame ss a b
pattern OpenGame{profiles, play, evaluate} = Generic.OpenGame profiles play evaluate
{-# COMPLETE OpenGame #-}

type Game :: CAT GAME
type Game = Generic.Game @Type

pattern Game :: forall a b. () => forall ss. OpenGame ss a b -> Game a b
pattern Game g = Generic.Game g
{-# COMPLETE Game #-}

type Strategy :: GAME -> GAME -> Type
type Strategy = Generic.Strategy @Type

pattern Context :: Observation a -> (Observation b -> Coutility b) -> Context a b
pattern Context x k <- (unpackContext -> (x, k))
  where
    Context x k = Generic.Context (\() -> ((), x)) (\((), y) -> k y)
{-# COMPLETE Context #-}

unpackContext :: Context a b -> (Observation a, Observation b -> Coutility b)
unpackContext (Generic.Context prior k) = let (z, x) = prior () in (x, \y -> k (z, y))

-- | Run a fixed strategy with the same forward residual on the backward pass.
runStrategy :: Strategy a b -> Context a b -> (Observation b, Coutility a)
runStrategy s c = Generic.runStrategy s c ()

outputs :: Strategy a b -> Observation a -> Observation b
outputs = Generic.outputs

-- | Lift a cartesian lens into a game with monoidal-lens behaviour.
fromLens :: Lens x s y r -> OpenGame '[] (G x s) (G y r)
fromLens optic = withLens optic \v u -> fromMonoidalLens (monLens (\x -> (x, v x)) u)

fromFunctions :: (x -> y) -> (r -> s) -> OpenGame '[] (G x s) (G y r)
fromFunctions = Generic.fromArrows

-- | A player observing @x@ and choosing @y@ to maximise the continuation's
-- utility. Enumerates all policies on the supplied finite observation domain.
-- Duplicates in either domain are removed. Supply every possible observation;
-- outside that domain the enumerated policies default to the first action.
-- A manually supplied policy must choose an action from the given action set.
-- An inadmissible choice is reported as out of equilibrium.
decision
  :: (Ord x, Show x, Ord y, Show y)
  => String -> NonEmpty x -> NonEmpty y -> OpenGame '[x -> y] (G x ()) (G y Payoff)
decision name xs actions@(fallback :| _) = OpenGame policies policyBehaviour check
  where
    observations = nubOrd (NE.toList xs)
    choices = nubOrd (NE.toList actions)
    policies =
      [ \x -> fromMaybe fallback (P.lookup x table)
      | table <- P.traverse (\x -> [(x, y) | y <- choices]) observations
      ]
    policyBehaviour policy = monLens (\x -> ((), policy x)) (P.const ())
    check policy (Context x k) =
      let chosen = policy x
          value = k chosen
          best = P.maximum (P.map k choices)
      in [ Diagnostic
             name
             (P.show x)
             (P.show chosen)
             value
             [P.show y | y <- choices, k y P.== best]
             best
             (chosen `P.elem` choices P.&& value P.>= best)
         ]

-- | A decision without an observation, taking @()@ as its SMC input.
choose :: (Ord y, Show y) => String -> NonEmpty y -> Game (G () ()) (G y Payoff)
choose name = decide name [()]

-- | A decision as a categorical 'Game', ready for SMC's @(-<)@.
-- Supply complete finite observation and action domains, as for 'decision'.
decide :: (Ord x, Show x, Ord y, Show y) => String -> NonEmpty x -> NonEmpty y -> Game (G x ()) (G y Payoff)
decide name xs ys = Game (decision name xs ys)

-- | Calculate backward returns from the forward values, keeping those values
-- as the game's outputs. For several decisions, supply a tuple of returns in
-- the same order as the tuple of input wires. Arbitrary return types are allowed.
payoffs :: (x -> s) -> Game (G x s) (G x ())
payoffs f = Game (fromLens (lens P.id (\(x, ()) -> f x)))

-- | Supply returns and close the game's forward outputs. This corresponds to
-- an empty @outputs@/@returns@ boundary in the open-game quasiquoter. The
-- choices remain visible in the equilibrium diagnostics.
finish :: (x -> s) -> Game (G x s) (G () ())
finish f = Game (fromLens (lens (P.const ()) (\(x, ()) -> f x)))

-- | Retain a value and its original payoff wire, and expose its observation to
-- a later decision. The observation-only copy has unit coutility, so observing
-- an action does not add the later player's utility to the earlier player's.
--
-- @
-- (retained, seen) <- observe action
-- response <- decide "Follower" observations actions -< seen
-- payoffs jointReturns -< (retained, response)
-- @
--
-- This is explicit observation sharing, not a global copying or feedback
-- structure on games. Both returned wires must be used by the SMC program.
observe
  :: forall x s d g d'
   . Term d g (F (G x s))
  -> Term d' g (F (G x s) :** F (G x ()))
observe value = lift @(F (G x s)) (Game (fromLens (lens (\x -> (x, x)) (\(_, (s, ())) -> s)))) (recast value)
