{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.OpenGame (test, Values (..), Table (..), table) where

import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Constraint, Type)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Examples.OpenGames.Bayesian qualified as B
import Examples.OpenGames.Deterministic
import Examples.OpenGames.Probability
import Proarrow.Category.Instance.Kleisli (KLEISLI (..))
import Proarrow.Category.Instance.OpenGame qualified as Generic
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Optic.Lens (lens)
import Proarrow.Optic.MonoidalLens (monLens)
import Proarrow.Testing
  ( GenTotal
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , check
  , expect
  , genNamed
  , genSomeDef
  , oneOfTotal
  , optGen
  )
import Proarrow.Testing.Laws (testCategory, testMonoidal, testProfunctor, testSymMonoidal)
import Props.Hask ()

test :: TestTree
test = testGroup "OpenGame" [deterministicTest, bayesianTest]

deterministicTest :: TestTree
deterministicTest =
  testGroup
    "Deterministic"
    [ testCategory @GAME
    , testProfunctor @Game
    , testMonoidal @GAME (\r -> r)
    , testSymMonoidal @GAME (\r -> r)
    , testProperty "semantic comparison observes play, backward play, diagnostics, and multiplicity" $ do
        let base, forwardChanged, backwardChanged, diagnosticsChanged, duplicated :: Game (G Bool Bool) (G Bool Bool)
            base = Game (fromFunctions id id)
            forwardChanged = Game (fromFunctions not id)
            backwardChanged = Game (fromFunctions id not)
            diagnosticsChanged =
              Game
                ( OpenGame @'[]
                    [()]
                    (const (monLens ((),) snd))
                    (\_ _ -> [Diagnostic "Player" "False" "False" 0 ["True"] 1 False])
                )
            duplicated = Game (OpenGame @'[] [(), ()] (const (monLens ((),) snd)) (\_ _ -> []))
        different <- traverse @[] (eqP base) [forwardChanged, backwardChanged, diagnosticsChanged, duplicated]
        check "semantic equality lost part of the game" (not (or different))
    ]

-- Finite observation domains and bounded utility probes. Products remain
-- testable, including the nested products introduced by the monoidal laws.
-- Rational coutilities are sampled at -1, 0, and 1; this is not an enumeration
-- of every rational context.
type Values :: Type -> Constraint
class (Ord a, Show a) => Values a where
  values :: NonEmpty a
  valueName :: String

instance Values () where
  values = [()]
  valueName = "()"

instance Values Bool where
  values = [False, True]
  valueName = "Bool"

instance Values Rational where
  values = [-1, 0, 1]
  valueName = "Payoff"

instance (Values a, Values b) => Values (a, b) where
  values = (,) <$> values @a <*> values @b
  valueName = "(" ++ valueName @a ++ ", " ++ valueName @b ++ ")"

instance (Ord a, Show a) => TestingEqShow (Distribution a)

instance (Values a) => Values (Distribution a) where
  values = (pure <$> values @a) <> [uniform (values @a)]
  valueName = "Distribution " ++ valueName @a

instance (Values a) => TestableType (Distribution a) where
  gen = do
    a <- optGen (NE.toList (values @a))
    b <- optGen (NE.toList (values @a))
    n <- optGen [0, 1, 2, 3]
    pure (either (error . show) id (weighted [(a, 1), (b, n)]))

instance Testable GAME where
  type TestOb a = (Ob a, Values (Observation a), Values (Coutility a))
  obFromTestOb r = r
  showOb @a = "G " ++ valueName @(Observation a) ++ " " ++ valueName @(Coutility a)
  genSome = genSomeDef @'[G () (), G Bool Payoff, G Bool Bool]

-- Generate finite tables directly, independently of the game operations being
-- tested. Lookups outside the bounded domain have a deterministic fallback.
table :: forall a b. (Values a, Values b) => GenTotal (a -> b)
table = do
  pairs <- traverse (\x -> (x,) <$> optGen (NE.toList (values @b))) (NE.toList (values @a))
  pure (\x -> fromMaybe (NE.head (values @b)) (lookup x pairs))

newtype Table a b = Table (a -> b)

instance (Values a, Values b) => TestingEqShow (Table a b) where
  showP (Table f) = show [(x, f x) | x <- NE.toList (values @a)]
  eqP (Table f) (Table g) = pure (all (\x -> f x == g x) (values @a))

instance (Values a, Values b) => TestableType (Table a b) where
  gen = Table <$> table

instance (TestOb a, TestOb b) => TestableType (Game a b) where
  gen =
    oneOfTotal
      [ (\v u -> Game (fromLens (lens v u))) <$> table <*> table
      , strategic
          <$> optGen ["Alice", "Bob", "Carol"]
          <*> table
          <*> table
          <*> table
          <*> table
          <*> table
      ]
    where
      -- A decision with two profiles, arbitrary play and backward tables,
      -- and genuine continuation-dependent best-response diagnostics. Keeping
      -- two profiles bounds the cost of composing several generated games.
      strategic name v0 v1 u0 u1 utility =
        Game $
          OpenGame @'[Bool]
            [False, True]
            (\s -> monLens (\x -> (x, view s x)) (update s))
            ( \s (Context x k) ->
                let score t = utility (k (view t x))
                    best = max (score False) (score True)
                in [ Diagnostic
                       name
                       (show x)
                       (show s)
                       (score s)
                       [show t | t <- [False, True], score t == best]
                       best
                       (score s >= best)
                   ]
            )
        where
          view s = if s then v1 else v0
          update s = if s then u1 else u0

-- Each strategy's signature keeps its behaviour across ALL probes together.
-- Sorting signatures then compares games up to one consistent strategy
-- bijection, rather than choosing a different matching for each context.
-- Diagnostic order is ignored; duplicate profiles and diagnostics are retained.
signature
  :: forall a b
   . (TestOb a, TestOb b)
  => [Observation b -> Coutility b]
  -> Game a b
  -> [[(Observation b, [Coutility a], [[Diagnostic]])]]
signature ks game =
  sort
    [ [ ( outputs s x
        , [snd (runStrategy s (Context x (const r))) | r <- NE.toList (values @(Coutility b))]
        , [sort (evaluateStrategy s (Context x k)) | k <- ks]
        )
      | x <- NE.toList (values @(Observation a))
      ]
    | s <- strategies game
    ]

instance (TestOb a, TestOb b) => TestingEqShow (Game a b) where
  eqP f g = do
    Table k1 <- genNamed @(Table (Observation b) (Coutility b)) "continuation 1"
    Table k2 <- genNamed @(Table (Observation b) (Coutility b)) "continuation 2"
    Table k3 <- genNamed @(Table (Observation b) (Coutility b)) "continuation 3"
    let ks = [k1, k2, k3, const (NE.head (values @(Coutility b))), const (NE.last (values @(Coutility b)))]
    pure (signature ks f == signature ks g)
  showP g = show (signature [const (NE.head (values @(Coutility b))), const (NE.last (values @(Coutility b)))] g)

instance TestableProfunctor Game

bayesianTest :: TestTree
bayesianTest =
  testGroup
    "Bayesian"
    [ testCategory @B.BAYESIAN
    , testProfunctor @B.Game
    , testMonoidal @B.BAYESIAN (\r -> r)
    , testSymMonoidal @B.BAYESIAN (\r -> r)
    , testProperty "diagnostic-free composition leaves unused play and context arrows lazy" $ do
        let noChecks :: B.OpenGame '[] (B.G Bool Bool) (B.G Bool Bool)
            noChecks = Generic.OpenGame [()] (\_ -> error "unused play was forced") (\_ _ -> [])
            game = Generic.Game (Generic.andThen (Generic.andThen noChecks noChecks) noChecks)
            ctx = Generic.Context @(KL ()) (error "unused prior was forced") (error "unused continuation was forced")
        expect "empty diagnostics" [[]] [B.evaluateStrategy s ctx | s <- B.strategies game]
    , testProperty "shared strategy closures preserve play, context dependence and profiles" $ do
        game <- genNamed @(B.Game (B.G Bool Bool) (B.G Bool Bool)) "game"
        same <- eqP game (Generic.memoisePlay game)
        check "sharing changed the game" same
    , testProperty "semantic comparison observes joint backward correlations" $ do
        let correlated, independent :: B.Game (B.G () Bool) (B.G Bool ())
            correlated =
              B.Game
                ( B.fromMonoidalLens
                    (B.behaviour (\() -> (\b -> (b, b)) <$> uniform (values @Bool)) (\(b, ()) -> pure b))
                )
            independent =
              B.Game
                ( B.fromMonoidalLens
                    (B.behaviour (\() -> (\b -> (b, b)) <$> uniform (values @Bool)) (\(_, ()) -> uniform (values @Bool)))
                )
        same <- eqP correlated independent
        check "comparator compared only marginals" (not same)
    ]

instance Testable B.BAYESIAN where
  type TestOb a = (Ob a, Values (B.Observation a), Values (B.Coutility a))
  obFromTestOb r = r
  showOb @a = "G " ++ valueName @(B.Observation a) ++ " " ++ valueName @(B.Coutility a)
  genSome = genSomeDef @'[B.G () (), B.G Bool B.Payoff, B.G Bool Bool]

instance (TestOb a, TestOb b) => TestableType (B.Game a b) where
  gen =
    oneOfTotal
      [ (\v u -> B.Game (B.fromMonoidalLens (B.behaviour v u)))
          <$> table @(B.Observation a) @(Distribution (Bool, B.Observation b))
          <*> table @(Bool, B.Coutility b) @(Distribution (B.Coutility a))
      , strategic
          <$> optGen ["Alice", "Bob", "Carol"]
          <*> table
          <*> table
          <*> table
          <*> table
          <*> table
      ]
    where
      -- Arbitrary stochastic forward/backward tables retain a shared Boolean
      -- residual. Diagnostics are genuine posterior expected best responses.
      strategic
        :: String
        -> (B.Observation a -> Distribution (Bool, B.Observation b))
        -> (B.Observation a -> Distribution (Bool, B.Observation b))
        -> ((Bool, B.Coutility b) -> Distribution (B.Coutility a))
        -> ((Bool, B.Coutility b) -> Distribution (B.Coutility a))
        -> (B.Coutility b -> B.Payoff)
        -> B.Game a b
      strategic name v0 v1 u0 u1 utility =
        B.Game $
          B.OpenGame @'[Bool]
            [False, True]
            (\s -> B.behaviour (view s) (update s))
            ( \s (B.Context prior k) ->
                [ let score t =
                        expectation
                          ( \(z, _) ->
                              expectation
                                (\(_, y) -> expectation utility (k z y))
                                (view t x)
                          )
                          posterior
                      best = max (score False) (score True)
                  in B.Diagnostic
                       name
                       (show x)
                       (show s)
                       (score s)
                       [show t | t <- [False, True], score t == best]
                       best
                       (score s >= best)
                | x <- nubOrd [x | ((_, x), _) <- weightedValues prior]
                , Just posterior <- [condition ((== x) . snd) prior]
                ]
            )
        where
          view s = if s then v1 else v0
          update s = if s then u1 else u0

-- One signature per strategy, across all sampled contexts, means equality
-- requires a consistent profile matching. Joint outcomes include backward
-- returns, preserving correlations rather than comparing separate marginals.
bayesianSignature
  :: (TestOb a, TestOb b)
  => [B.Context a b]
  -> B.Game a b
  -> [[([((B.Observation b, B.Coutility a), Rational)], [B.Diagnostic])]]
bayesianSignature cs g =
  sort
    [ [(probabilities (B.runStrategy s c), sort (B.evaluateStrategy s c)) | c <- cs]
    | s <- B.strategies g
    ]

instance (TestOb a, TestOb b) => TestingEqShow (B.Game a b) where
  eqP f g = do
    prior1 <- genNamed @(Distribution (Bool, B.Observation a)) "joint hidden-state prior 1"
    prior2 <- genNamed @(Distribution (Bool, B.Observation a)) "joint hidden-state prior 2"
    Table k1 <- genNamed @(Table (Bool, B.Observation b) (Distribution (B.Coutility b))) "stochastic continuation 1"
    Table k2 <- genNamed @(Table (Bool, B.Observation b) (Distribution (B.Coutility b))) "stochastic continuation 2"
    let cs =
          [B.Context prior1 (curry k1), B.Context prior2 (curry k2)]
            ++ [B.Context (pure (z, x)) (curry k1) | z <- [False, True], x <- NE.toList (values @(B.Observation a))]
    pure (bayesianSignature cs f == bayesianSignature cs g)
  showP g =
    show
      ( bayesianSignature
          [ B.context x (const r)
          | x <- NE.toList (values @(B.Observation a))
          , r <- [NE.head (values @(B.Coutility b)), NE.last (values @(B.Coutility b))]
          ]
          g
      )

instance TestableProfunctor B.Game
