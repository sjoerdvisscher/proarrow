{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}

-- | Finite Bayesian open games with exact probability, behavioural policies,
-- and explicit finite strategy catalogues. Hidden state remains in a joint
-- context distribution and is conditioned on each player's observation.
-- Sequential composition and independent parallel play form a symmetric
-- monoidal category, modulo strategy bijections and diagnostic permutations.
--
-- The SMC helpers mirror "Examples.OpenGames.Deterministic". 'choose' and
-- 'decide' enumerate pure policies; 'chooseMixed' and 'decideMixed' accept a
-- finite catalogue of candidate randomisations. Evaluation checks deviations
-- to /all/ legal pure actions, including ones outside the candidate catalogue.
-- It does not search the continuum of mixtures or impose subgame perfection.
--
-- This specialises "Proarrow.Category.Instance.OpenGame" to Kleisli arrows.
-- Play is a 'MonoidalLens' in the distribution Kleisli category. Use
-- 'behaviour' to supply stochastic legs and 'fromMonoidalLens' for a nonstrategic
-- component; the game backend handles their Kleisli wrapping.
module Examples.OpenGames.Bayesian
  ( Stochastic
  , pattern Stochastic
  , BAYESIAN
  , G
  , Observation
  , Coutility
  , Context
  , pattern Context
  , context
  , stochasticContext
  , Payoff
  , Diagnostic (..)
  , isEquilibrium
  , behaviour
  , OpenGame
  , pattern OpenGame
  , profiles
  , strategy
  , play
  , evaluate
  , Game
  , pattern Game
  , Strategy
  , pattern Strategy
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
  , cachePlay
  , cacheLens
  , parallel
  , reindex
  , decision
  , mixedDecision
  , nature
  , liftStochastic
  , choose
  , decide
  , chooseMixed
  , decideMixed
  , payoffs
  , finish
  , observe
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Lazy qualified as M
import Data.Maybe (fromMaybe)
import Prelude hiding (id, (**), (.))

import Examples.OpenGames.Probability (Distribution, collect, condition, expectation, probabilities, weightedValues)
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..), arr)
import Proarrow.Category.Instance.OpenGame
  ( Diagnostic (..)
  , Payoff
  , equilibria
  , evaluate
  , evaluateStrategy
  , fromMonoidalLens
  , isEquilibrium
  , parallel
  , play
  , playStrategy
  , reindex
  , strategies
  , withGame
  )
import Proarrow.Category.Instance.OpenGame qualified as Generic
import Proarrow.Category.Monoidal.Strictified (Fold)
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), UN)
import Proarrow.Functor qualified as F
import Proarrow.Optic.Lens (Lens, lens, withLens)
import Proarrow.Optic.MonoidalLens (MonoidalLens, monLens, withMonLens)
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Promonad.Pure (WithPure (Pure), liftWithPure, lowerWithPure)
import Proarrow.Tools.SMC (SYN (..), Term, lift, recast)

type Stochastic = KLEISLI (WithPure (Star (F.Prelude Distribution)))

-- Interpret only where a distribution function is required for execution.
pattern Stochastic :: (x -> F.Prelude Distribution y) -> Kleisli (KL x :: Stochastic) (KL y)
pattern Stochastic f <- Kleisli (lowerWithPure -> Star f)
  where
    Stochastic f = Kleisli (liftWithPure (Star f))
{-# COMPLETE Stochastic #-}

type BAYESIAN = Generic.GAME Stochastic

type G :: Type -> Type -> BAYESIAN
type G x s = Generic.G (KL x) (KL s)

type Observation :: BAYESIAN -> Type
type Observation a = UN KL (Generic.Observation a)

type Coutility :: BAYESIAN -> Type
type Coutility a = UN KL (Generic.Coutility a)

type Context :: BAYESIAN -> BAYESIAN -> Type
type Context a b = Generic.Context @Stochastic a b

type OpenGame :: [Type] -> BAYESIAN -> BAYESIAN -> Type
type OpenGame = Generic.OpenGame @Stochastic

pattern OpenGame
  :: forall ss a b
   . ()
  => (Ob ss, Ob a, Ob b)
  => [Fold ss] -> (Fold ss -> Strategy a b) -> OpenGame ss a b
pattern OpenGame{profiles, strategy} = Generic.OpenGame profiles strategy
{-# COMPLETE OpenGame #-}

type Game :: CAT BAYESIAN
type Game = Generic.Game @Stochastic

pattern Game :: forall a b. () => forall ss. OpenGame ss a b -> Game a b
pattern Game g = Generic.Game g
{-# COMPLETE Game #-}

type Strategy :: BAYESIAN -> BAYESIAN -> Type
type Strategy = Generic.Strategy @Stochastic

pattern Strategy
  :: forall a b
   . ()
  => (Ob a, Ob b)
  => MonoidalLens (Generic.Observation a) (Generic.Coutility a) (Generic.Observation b) (Generic.Coutility b)
  -> (Context a b -> [Diagnostic])
  -> Strategy a b
pattern Strategy optic check = Generic.Strategy optic check
{-# COMPLETE Strategy #-}

-- | Construct behaviour from stochastic forward and backward legs sharing a
-- residual. The wrapping into Kleisli arrows is local to the game backend.
behaviour
  :: forall m x s y r
   . (x -> Distribution (m, y)) -> ((m, r) -> Distribution s) -> MonoidalLens (KL x :: Stochastic) (KL s) (KL y) (KL r)
behaviour forward backward =
  monLens @(KL m)
    (Stochastic (F.Prelude . forward))
    (Stochastic (F.Prelude . backward))

data ContextParts x y r where
  ContextParts :: Distribution (z, x) -> (z -> y -> Distribution r) -> ContextParts x y r

unpackContext :: MonoidalLens (KL () :: Stochastic) (KL r) (KL x) (KL y) -> ContextParts x y r
unpackContext optic = withMonLens optic \_ (Stochastic forward) (Stochastic backward) ->
  ContextParts (unState forward) (unContinuation backward)

pattern Context
  :: forall x y r
   . ()
  => forall z
   . Distribution (z, x)
  -> (z -> y -> Distribution r)
  -> MonoidalLens (KL () :: Stochastic) (KL r) (KL x) (KL y)
pattern Context prior k <- (unpackContext -> ContextParts prior k)
  where
    Context prior k = behaviour (\() -> prior) (\(z, y) -> k z y)
{-# COMPLETE Context #-}

unState :: (() -> F.Prelude Distribution a) -> Distribution a
unState f = F.unPrelude (f ())

unContinuation :: ((z, y) -> F.Prelude Distribution r) -> z -> y -> Distribution r
unContinuation f z y = F.unPrelude (f (z, y))

-- | A deterministic observation and deterministic continuation.
context :: x -> (y -> r) -> MonoidalLens (KL () :: Stochastic) (KL r) (KL x) (KL y)
context x k = stochasticContext (pure x) (pure . k)

-- | A stochastic context with no additional hidden state. Use 'Context' itself
-- when observations and the continuation share a latent variable.
stochasticContext
  :: Distribution x -> (y -> Distribution r) -> MonoidalLens (KL () :: Stochastic) (KL r) (KL x) (KL y)
stochasticContext prior k = Context (((),) <$> prior) (\() -> k)

-- | Execute a fixed strategy in its full context, retaining the joint output
-- and source coutility. Forward and backward passes share the sampled residual.
runStrategy :: Strategy a b -> Context a b -> Distribution (Observation b, Coutility a)
runStrategy s@Generic.Strategy{} c = case Generic.runStrategy s c of
  Stochastic f -> unState f

outputs :: Strategy a b -> Distribution (Observation a) -> Distribution (Observation b)
outputs s@Generic.Strategy{} prior = case Generic.outputs s of
  Stochastic forward -> prior >>= (F.unPrelude . forward)

fromLens :: Lens x s y r -> OpenGame '[] (G x s) (G y r)
fromLens optic = withLens optic \v u ->
  fromMonoidalLens (behaviour (\x -> pure (x, v x)) (pure . u))

fromFunctions :: (x -> y) -> (r -> s) -> OpenGame '[] (G x s) (G y r)
fromFunctions f g = Generic.fromArrows (arr f) (arr g)

-- | Cache a selected profile's finite play kernel. The return domain must
-- include every possible coutility supplied by its environment. Each residual
-- is represented by its conditional backward distributions, preserving its
-- correlation with the forward output. Equal residual/output pairs are merged.
-- Inputs outside the supplied cache domain are computed on demand.
-- Diagnostic evaluation is unchanged; its upstream callers use the cached play.
cachePlay
  :: forall x s y r
   . (Ord x, Ord s, Ord y, Ord r)
  => NonEmpty x -> NonEmpty r -> Game (G x s) (G y r) -> Game (G x s) (G y r)
cachePlay xs rs (Generic.Game (g@Generic.OpenGame{} :: OpenGame ss (G x s) (G y r))) =
  Generic.memoisePlay (Generic.Game (Generic.OpenGame @ss (profiles g) cachedStrategy))
  where
    cachedStrategy s = case strategy g s of
      Strategy optic check -> Strategy (cacheLens xs rs optic) check

-- | Tabulate a finite stochastic lens while retaining joint residual/output
-- probabilities. The return domain must cover every supplied coutility.
cacheLens
  :: forall x s y r
   . (Ord x, Ord s, Ord y, Ord r)
  => NonEmpty x
  -> NonEmpty r
  -> MonoidalLens (KL x :: Stochastic) (KL s) (KL y) (KL r)
  -> MonoidalLens (KL x :: Stochastic) (KL s) (KL y) (KL r)
cacheLens xs rs optic = withMonLens optic \_ (Stochastic forward) backwardArrow ->
  case backwardArrow of
    Kleisli (Pure backward) ->
      let kernel x =
            collect $
              (\(m, y) -> (M.fromList [(r, backward (m, r)) | r <- NE.toList rs], y))
                <$> F.unPrelude (forward x)
          table = M.fromList [(x, kernel x) | x <- NE.toList xs]
      in monLens @(KL (M.Map r s))
           (Stochastic (F.Prelude . (\x -> M.findWithDefault (kernel x) x table)))
           (arr (uncurry (M.!)))
    Stochastic backward ->
      let kernel x =
            collect $
              (\(m, y) -> (M.fromList [(r, collect (F.unPrelude (backward (m, r)))) | r <- NE.toList rs], y))
                <$> F.unPrelude (forward x)
          table = M.fromList [(x, kernel x) | x <- NE.toList xs]
      in behaviour (\x -> M.findWithDefault (kernel x) x table) (uncurry (M.!))

-- | Enumerate pure policies on a complete finite observation/action domain.
decision
  :: (Ord x, Show x, Ord y, Show y)
  => String -> NonEmpty x -> NonEmpty y -> OpenGame '[x -> Distribution y] (G x ()) (G y Payoff)
decision name xs ys = mixedDecision name xs ys (pure <$> ys)

-- | Enumerate policies from candidate action distributions. Their supports
-- must lie in the legal action domain; evaluation rejects inadmissible policies.
-- Expected utility is conditioned on each positive-probability observation.
-- A manually supplied policy may use any finite rational distribution.
mixedDecision
  :: (Ord x, Show x, Ord y, Show y)
  => String
  -> NonEmpty x
  -> NonEmpty y
  -> NonEmpty (Distribution y)
  -> OpenGame '[x -> Distribution y] (G x ()) (G y Payoff)
mixedDecision name xs ys candidates = OpenGame policies (\policy -> Strategy (policyBehaviour policy) (check policy))
  where
    observations = nubOrd (NE.toList xs)
    actions = nubOrd (NE.toList ys)
    mixtures = nubOrd (NE.toList candidates)
    policies =
      [ \x -> fromMaybe (NE.head candidates) (lookup x table)
      | table <- traverse (\x -> [(x, p) | p <- mixtures]) observations
      ]
    policyBehaviour policy =
      behaviour
        (fmap ((),) . policy)
        (\((), _) -> pure ())
    check policy (Context prior k) =
      [ let utilities = M.fromList [(y, expectation (\(z, _) -> expectation id (k z y)) posterior) | y <- actions]
            utility y = M.findWithDefault (expectation (\(z, _) -> expectation id (k z y)) posterior) y utilities
            chosen = policy x
            value = expectation utility chosen
            best = maximum (map utility actions)
            legal = all (\(y, _) -> y `elem` actions) (weightedValues chosen)
            display = case probabilities chosen of
              [(y, 1)] -> show y
              _ -> show chosen
        in Diagnostic
             name
             (show x)
             display
             value
             [show y | y <- actions, utility y == best]
             best
             (legal && value >= best)
      | x <- nubOrd [x | ((_, x), _) <- weightedValues prior]
      , Just posterior <- [condition ((== x) . snd) prior]
      ]

nature :: Distribution x -> Game (G () ()) (G x ())
nature p = liftStochastic (const p)

liftStochastic :: (x -> Distribution y) -> Game (G x ()) (G y ())
liftStochastic f = Game (fromMonoidalLens (behaviour (fmap ((),) . f) (\((), ()) -> pure ())))

choose :: (Ord y, Show y) => String -> NonEmpty y -> Game (G () ()) (G y Payoff)
choose name = decide name [()]

decide :: (Ord x, Show x, Ord y, Show y) => String -> NonEmpty x -> NonEmpty y -> Game (G x ()) (G y Payoff)
decide name xs ys = Game (decision name xs ys)

chooseMixed :: (Ord y, Show y) => String -> NonEmpty y -> NonEmpty (Distribution y) -> Game (G () ()) (G y Payoff)
chooseMixed name = decideMixed name [()]

decideMixed
  :: (Ord x, Show x, Ord y, Show y)
  => String -> NonEmpty x -> NonEmpty y -> NonEmpty (Distribution y) -> Game (G x ()) (G y Payoff)
decideMixed name xs ys ps = Game (mixedDecision name xs ys ps)

payoffs :: (x -> s) -> Game (G x s) (G x ())
payoffs f = Game (fromLens (lens id (\(x, ()) -> f x)))

finish :: (x -> s) -> Game (G x s) (G () ())
finish f = Game (fromLens (lens (const ()) (\(x, ()) -> f x)))

observe
  :: forall x s d g d'
   . Term d g (F (G x s))
  -> Term d' g (F (G x s) :** F (G x ()))
observe value =
  lift @(F (G x s))
    (Game (fromLens (lens (\x -> (x, x)) (\(_, (s, ())) -> s))))
    (recast value)
