{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QualifiedDo #-}

module Examples.OpenGames
  ( test
  , prisonersDilemma
  , prisonersDilemmaClosed
  , sequentialGame
  , matchingPennies
  , privateSignal
  , sequentialResponses
  ) where

import Data.List (sort)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Examples.OpenGames.Bayesian qualified as B
import Examples.OpenGames.Deterministic
import Examples.OpenGames.Probability
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..), arr)
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..), singleton, swap2)
import Proarrow.Core (Promonad (..))
import Proarrow.Functor (Prelude (..))
import Proarrow.Optic.Getter (view)
import Proarrow.Optic.Lens (lens)
import Proarrow.Optic.MonoidalLens (MonoidalLens, monLens, withMonLens)
import Proarrow.Promonad.Pure (WithPure (Pure))
import Proarrow.Testing (check, expect, testEq)
import Proarrow.Tools.SMC (SYN (..), toSMC, (-<))
import Proarrow.Tools.SMC qualified as SMC
import Props.OpenGame ()

data Action = Cooperate | Defect deriving (Eq, Ord, Show)

-- Two independent choices, coupled through a common continuation.
prisonersDilemma
  :: Game (G () ()) (G (Action, Action) ())
prisonersDilemma = toSMC @I \() -> SMC.do
  a <- choose "Alice" [Cooperate, Defect]
  b <- choose "Bob" [Cooperate, Defect]
  payoffs pdPayoff -< (a, b)

-- The same empty boundary as the upstream [opengame| ... |] example.
prisonersDilemmaClosed :: Game (G () ()) (G () ())
prisonersDilemmaClosed = toSMC @I \() -> SMC.do
  a <- choose "Alice" [Cooperate, Defect]
  b <- choose "Bob" [Cooperate, Defect]
  finish pdPayoff -< (a, b)

-- Replacing just the ordinary payoff function changes the strategic game.
simultaneous :: ((Bool, Bool) -> (Payoff, Payoff)) -> Game (G () ()) (G () ())
simultaneous returns = toSMC @I \() -> SMC.do
  a <- choose "Alice" [False, True]
  b <- choose "Bob" [False, True]
  finish returns -< (a, b)

-- Observe an older variable after another decision has introduced a binder.
-- This exercises SMC's depth adaptation as well as independent payoff wires.
delayedObservation :: Game (G () ()) (G ((Bool, Bool), Bool) ())
delayedObservation = toSMC @I \() -> SMC.do
  a <- choose "Leader" [False, True]
  b <- choose "Independent" [False, True]
  (retained, seen) <- observe a
  c <- decide "Follower" [False, True] [False, True] -< seen
  payoffs delayedReturns -< (retained, b, c)

delayedReturns :: ((Bool, Bool), Bool) -> ((Payoff, Payoff), Payoff)
delayedReturns ((a, b), c) = ((if a == c then 1 else 0, if b then 2 else -1), if c then 3 else -2)

-- An independent description with categorical combinators, for comparison.
prisonersDilemmaExplicit :: Game (G () ()) (G (Action, Action) ())
prisonersDilemmaExplicit = returns . (player1 ** player2) . prepare
  where
    player1 = Game (decision "Alice" [()] [Cooperate, Defect])
    player2 = Game (decision "Bob" [()] [Cooperate, Defect])
    prepare = Game (fromFunctions (\() -> ((), ())) (const ()))
    returns = Game (fromLens (lens id (\(actions, ()) -> pdPayoff actions)))

pdPayoff :: (Action, Action) -> (Payoff, Payoff)
pdPayoff (Cooperate, Cooperate) = (3, 3)
pdPayoff (Cooperate, Defect) = (0, 5)
pdPayoff (Defect, Cooperate) = (5, 0)
pdPayoff (Defect, Defect) = (1, 1)

-- The follower observes the leader's action. Its policy must be run again
-- for a counterfactual leader action, not frozen at the actual observation.
sequentialGame
  :: Game (G () ()) (G (Bool, Bool) Payoff)
sequentialGame = toSMC @I \() -> SMC.do
  a <- choose "Leader" [False, True]
  (retained, seen) <- observe a
  b <- decide "Follower" [False, True] [False, True] -< seen
  sharedPayoff -< (retained, b)
  where
    sharedPayoff = Game (fromFunctions id (\r -> (r, r)))

sequentialGameExplicit :: Game (G () ()) (G (Bool, Bool) Payoff)
sequentialGameExplicit = sharedPayoff . (id ** follower) . remember . leader
  where
    leader = Game (decision "Leader" [()] [False, True])
    follower = Game (decision "Follower" [False, True] [False, True])
    -- Explicit wiring retains the observation and returns the leader's payoff.
    remember = Game (fromLens (lens (\x -> (x, x)) (\(_, (r, ())) -> r)))
    sharedPayoff = Game (fromFunctions id (\r -> (r, r)))

-- A repeated decision with a nontrivial backward pass, used to check laws.
type B :: GAME
type B = G Bool Payoff

roundGame :: String -> OpenGame '[Bool -> Bool] B B
roundGame name =
  OpenGame
    (profiles choice)
    ( \policy ->
        Strategy
          (monLens (\x -> (x, policy x)) (\(x, r) -> if x then r + 1 else r - 1))
          (evaluate choice policy)
    )
  where
    choice = decision name [False, True] [False, True]

test :: TestTree
test = testGroup "Open games" [deterministicTest, bayesianTest]

deterministicTest :: TestTree
deterministicTest =
  testGroup
    "Deterministic"
    [ testProperty "Prisoner's Dilemma has only mutual defection in equilibrium" $ do
        let g = prisonersDilemma
            context = Context () (const ())
            solutions = equilibria g context
        check "wrong equilibria" (map (`outputs` ()) solutions == [(Defect, Defect)])
        let ds =
              concat
                [evaluateStrategy s context | s <- strategies g, outputs s () == (Cooperate, Cooperate)]
        check "both players should want to deviate" (map equilibrium ds == [False, False])
        check "deviation payoffs" (map payoff ds == [3, 3] && map optimalPayoff ds == [5, 5])
        check "enumeration lost a strategy" (length (strategies g) == 4)
        check "solution could not be replayed" (map (\s -> map payoff (evaluateStrategy s context)) solutions == [[1, 1]])
    , testProperty "SMC syntax preserves all Prisoner's Dilemma profiles and diagnostics" $ do
        let context = Context () (const ())
            reports game =
              sort
                [(outputs s (), evaluateStrategy s context) | s <- strategies game]
        check
          "SMC changed simultaneous play or returns"
          (reports prisonersDilemma == reports prisonersDilemmaExplicit)
    , testProperty "finish closes outputs while preserving equilibrium diagnostics" $ do
        let context = Context () (const ())
            solutions = equilibria prisonersDilemmaClosed context
        check "closed boundary changed the strategy space" (length (strategies prisonersDilemmaClosed) == 4)
        check
          "closed game lost the equilibrium"
          (map (map chosenAction . (`evaluateStrategy` context)) solutions == [["Defect", "Defect"]])
        check
          "closed game lost backward returns"
          (map (map payoff . (`evaluateStrategy` context)) solutions == [[1, 1]])
    , testProperty "SMC models coordination and matching pennies by changing payoffs" $ do
        let context = Context () (const ())
            coordination = simultaneous (\(a, b) -> if a == b then (1, 1) else (0, 0))
            pureMatchingPennies = simultaneous (\(a, b) -> if a == b then (1, 0) else (0, 1))
            reports game = sort [map chosenAction (evaluateStrategy s context) | s <- equilibria game context]
        check
          "wrong coordination equilibria"
          (reports coordination == [["False", "False"], ["True", "True"]])
        check "matching pennies should have no pure equilibrium" (null (equilibria pureMatchingPennies context))
    , testProperty "SMC observation sharing preserves sequential counterfactuals" $
        testEq "SMC sequential game" "SMC" sequentialGame "explicit composition" sequentialGameExplicit
    , testProperty "SMC observes an older action without conflating players or returns" $ do
        let g = delayedObservation
            context = Context () (const ())
        check "lost a decision or follower policy" (length (strategies g) == 16)
        check "observation sharing changed player utilities" $
          all
            ( \s ->
                let ((a, b), c) = delayedReturns (outputs s ())
                in map payoff (evaluateStrategy s context) == [a, b, c]
            )
            (strategies g)
        check "observation sharing changed player identities" $
          all (\s -> map player (evaluateStrategy s context) == ["Leader", "Independent", "Follower"]) (strategies g)
    , testProperty "sequential deviations rerun the follower's policy" $ do
        let g = sequentialGame
            k (x, y) = if x == y then (if x then 2 else 1) else 0
            -- Two policies produce this outcome but respond differently to
            -- a counterfactual leader move. Inspect both through Game's API.
            checks =
              sort
                [ (map optimalPayoff ds, map equilibrium ds)
                | s <- strategies g
                , outputs s () == (False, True)
                , let ds = evaluateStrategy s (Context () k)
                ]
        -- With the opposite-action policy, both possible leader actions earn 0.
        check
          "leader's counterfactual policy was frozen, or follower deviation lost"
          (checks == [([0, 1], [True, False]), ([2, 1], [False, False])])
        let outcomes =
              [outputs s () | s <- equilibria g (Context () k)]
        -- The low-payoff equilibrium uses an off-path threat. These are Nash
        -- checks at reached observations, not subgame-perfect equilibrium checks.
        -- Two follower policies support (True, True), differing off the path.
        check "wrong reached-observation equilibria" (sort outcomes == [(False, False), (True, True), (True, True)])
    , testProperty "Game values with different hidden strategy types share a collection" $ do
        let choice = Game (decision "Player" [()] [False, True])
            reward = Game (fromLens (lens (const ()) (\(y, ()) -> if y then 1 else 0)))
            close = Game (fromFunctions (const ()) id)
            games :: [Game (G () ()) (G () ())]
            games = [id, reward . choice, close . prisonersDilemma]
            context = Context () (const ())
            solutions = map (`equilibria` context) games
        check "lost hidden strategy catalogues" (map (length . strategies) games == [1, 2, 4])
        check "could not solve composed Game values" (map length solutions == [1, 1, 1])
        check
          "lost player diagnostics"
          (map (map (\s -> length (evaluateStrategy s context))) solutions == [[0], [1], [2]])
    , testProperty "a selected Game strategy can be stored and reevaluated" $ do
        let g = Game (decision "Policy" [False, True] [False, True])
            utility y = if y then 1 else 0
            selected =
              [s | s <- equilibria g (Context True utility), not (outputs s False), outputs s True]
        check "could not select the identity policy" (length selected == 1)
        check
          "selected strategy lost forward behaviour"
          (map (\s -> (outputs s False, outputs s True)) selected == [(False, True)])
        check
          "equilibrium result was frozen to the original context"
          (map (\s -> isEquilibrium (evaluateStrategy s (Context False utility))) selected == [False])
        check
          "backward play unavailable"
          (map (\s -> snd (runStrategy s (Context True (const 1)))) selected == [()])
    , testProperty "monoidal-lens behaviour retains its explicit residual" $ do
        let game :: Game (G Int Int) (G Int Int)
            game = Game (fromMonoidalLens (monLens (\x -> (x * x, x + 1)) (uncurry (+))))
        check "forward behaviour lost" (map (`outputs` 5) (strategies game) == [6])
        check
          "backward behaviour lost the residual"
          (map (\s -> runStrategy s (Context 5 (const 2))) (strategies game) == [(6, 27)])
    , testProperty "ties are equilibria and report every optimal action" $ do
        let g = decision "Player" [()] [False, True]
            ds = evaluate g (const True) (Context () (const 7))
        check "tie rejected" (isEquilibrium ds)
        check "missing tied actions" (map optimalActions ds == [["False", "True"]])
    , testProperty "finite policies are enumerated without duplicate domain entries" $ do
        let g = decision "Player" [False, True, False] [False, True, True]
        check
          "expected all four policies"
          ( sort ([[p False, p True] | p <- profiles g] :: [[Bool]])
              == [[False, False], [False, True], [True, False], [True, True]]
          )
    , testProperty "inadmissible manual strategies are rejected" $ do
        let g = decision "Player" [()] [Cooperate]
        check "out-of-domain action accepted" (not (isEquilibrium (evaluate g (const Defect) (Context () (const 0)))))
    , testProperty "reindexing uses the strictified strategy coordinates" $ do
        let g = parallel (roundGame "left") (roundGame "right")
            permuted = reindex (profiles g) (swap2 @(Bool -> Bool) @(Bool -> Bool)) g
        testEq "profile bijection" "permuted" (Game permuted) "original" (Game g)
    , testProperty "the games category works under Strictified" $ do
        let f = singleton (Game (roundGame "f"))
            g = singleton (Game (roundGame "g"))
            result = unStr (f ** g)
            result' = unStr ((f ** id @Strictified @'[]) ** g)
        testEq "strict tensor" "strictified" result "parallel" (Game (parallel (roundGame "f") (roundGame "g")))
        testEq "strict empty unit" "with empty unit" result' "without empty unit" result
    ]

coin :: Distribution Bool
coin = uniform [False, True]

-- Both the fair mixture and its pure deviations are explicit candidates.
matchingPennies :: B.Game (B.G () ()) (B.G (Bool, Bool) ())
matchingPennies = toSMC @I \() -> SMC.do
  a <- B.chooseMixed "Alice" [False, True] [pure False, pure True, coin]
  b <- B.chooseMixed "Bob" [False, True] [pure False, pure True, coin]
  B.payoffs (\(alice, bob) -> if alice == bob then (1, 0) else (0, 1)) -< (a, b)

-- A chance variable is retained for settlement, while the player sees only
-- a noisy signal. Correct inference earns 3/4, rather than clairvoyant B.payoff 1.
privateSignal :: B.Game (B.G () ()) (B.G (Bool, Bool) ())
privateSignal = toSMC @I \() -> SMC.do
  truth <- B.nature coin
  (retained, unseen) <- B.observe truth
  signal <- B.liftStochastic noisy -< unseen
  guess <- B.decide "Guesser" [False, True] [False, True] -< signal
  B.payoffs (\(actual, prediction) -> ((), if actual == prediction then 1 else 0)) -< (retained, guess)
  where
    noisy truth = either (error . show) id (weighted [(truth, 3), (not truth, 1)])

sharedReturn :: (Bool, Bool) -> B.Payoff
sharedReturn (a, b) = if a == b then (if a then 2 else 1) else 0

sequentialResponses :: B.Game (B.G () ()) (B.G (Bool, Bool) ())
sequentialResponses = toSMC @I \() -> SMC.do
  a <- B.choose "Leader" [False, True]
  (retained, seen) <- B.observe a
  b <- B.decideMixed "Follower" [False, True] [False, True] [pure False, pure True, coin] -< seen
  B.payoffs (\ab -> (sharedReturn ab, sharedReturn ab)) -< (retained, b)

purePD :: B.Game (B.G () ()) (B.G (Bool, Bool) ())
purePD = toSMC @I \() -> SMC.do
  a <- B.choose "Alice" [False, True]
  b <- B.choose "Bob" [False, True]
  B.payoffs pdReturns -< (a, b)

deterministicPD :: Game (G () ()) (G (Bool, Bool) ())
deterministicPD = toSMC @I \() -> SMC.do
  a <- choose "Alice" [False, True]
  b <- choose "Bob" [False, True]
  payoffs pdReturns -< (a, b)

pdReturns :: (Bool, Bool) -> (B.Payoff, B.Payoff)
pdReturns (False, False) = (3, 3)
pdReturns (False, True) = (0, 5)
pdReturns (True, False) = (5, 0)
pdReturns (True, True) = (1, 1)

bayesianTest :: TestTree
bayesianTest =
  testGroup
    "Bayesian"
    [ testProperty "matching pennies has an exact fair mixed equilibrium" $ do
        let c = B.context () (const ())
            solutions = B.equilibria matchingPennies c
            reports = [B.evaluateStrategy s c | s <- solutions]
        expect "candidate profiles" 9 (length (B.strategies matchingPennies))
        expect "mixed equilibria" 1 (length solutions)
        expect "expected utilities" [[1 / 2, 1 / 2]] (map (map B.payoff) reports)
        expect "best responses" [[1 / 2, 1 / 2]] (map (map B.optimalPayoff) reports)
        expect "all pure actions are tied" [[["False", "True"], ["False", "True"]]] (map (map B.optimalActions) reports)
        expect
          "independent randomisation"
          [[((False, False), 1 / 4), ((False, True), 1 / 4), ((True, False), 1 / 4), ((True, True), 1 / 4)]]
          [probabilities (B.outputs s (pure ())) | s <- solutions]
    , testProperty "deviations are checked outside the mixed candidate catalogue" $ do
        let g = B.chooseMixed "Player" [False, True] [coin]
            c = B.context () (\y -> if y then 1 else 0)
            reports = [B.evaluateStrategy s c | s <- B.strategies g]
        check "a suboptimal singleton catalogue was accepted" (null (B.equilibria g c))
        expect "mixture utility" [[1 / 2]] (map (map B.payoff) reports)
        expect "pure deviation" [[1]] (map (map B.optimalPayoff) reports)
    , testProperty "private signals condition payoffs on the player's information" $ do
        let c = B.context () (const ())
            solutions = B.equilibria privateSignal c
        expect "truthful signal policy" 1 (length solutions)
        expect
          "posterior expected payoffs"
          [[3 / 4, 3 / 4]]
          [map B.payoff (B.evaluateStrategy s c) | s <- solutions]
        expect
          "guess is right three quarters of the time"
          [3 / 4]
          [probability (uncurry (==)) (B.outputs s (pure ())) | s <- solutions]
    , testProperty "explicit hidden-state contexts use the posterior, not the marginal" $ do
        let prior = either (error . show) id (weighted [((False, False), 3), ((True, False), 1), ((False, True), 1), ((True, True), 3)])
            c = B.Context prior (\truth guess -> pure (if truth == guess then 1 else 0))
            g = B.decide "Guesser" [False, True] [False, True]
            solutions = B.equilibria g c
        expect "Bayesian policy" 1 (length solutions)
        expect "conditional utility" [[3 / 4, 3 / 4]] [map B.payoff (B.evaluateStrategy s c) | s <- solutions]
        expect "conditional choices" [["False", "True"]] [map B.chosenAction (B.evaluateStrategy s c) | s <- solutions]
    , testProperty "parallel evaluation preserves correlated inputs and hidden state" $ do
        let g = B.decide "Alice" [False, True] [False, True] ** B.decide "Bob" [False, True] [False, True]
            prior = (\truth -> (truth, (truth, truth))) <$> coin
            c = B.Context prior (\truth (a, b) -> pure (if a == truth then 1 else 0, if b == truth then 1 else 0))
            solutions = B.equilibria g c
        expect "both players use their signal" 1 (length solutions)
        expect "correlated types were factorised" [[1, 1, 1, 1]] [map B.payoff (B.evaluateStrategy s c) | s <- solutions]
    , testProperty "sequential counterfactuals rerun stochastic responses" $ do
        let c = B.context () (const ())
            target = (False,) <$> coin
            selected = [s | s <- B.strategies sequentialResponses, B.outputs s (pure ()) == target]
            reports = [B.evaluateStrategy s c | s <- selected]
        expect "policies differ at the unreached observation" 3 (length selected)
        expect "actual expected return" [[1 / 2, 1 / 2], [1 / 2, 1 / 2], [1 / 2, 1 / 2]] (map (map B.payoff) reports)
        expect "counterfactual expected returns" [1 / 2, 1, 2] (sort [B.optimalPayoff d | d : _ <- reports])
    , testProperty "game behaviour uses the same sampled residual backward" $ do
        let optic = B.behaviour (\() -> (\b -> (b, b)) <$> coin) (\(b, r) -> pure (b == r))
            game = B.Game (B.fromMonoidalLens optic)
            results = [probabilities (B.runStrategy s (B.context () id)) | s <- B.strategies game]
        expect "residual was resampled" [[((False, True), 1 / 2), ((True, True), 1 / 2)]] results
    , testProperty "cached play preserves joint stochastic returns and uncached inputs" $ do
        let optic =
              B.behaviour
                (\x -> (\m -> (m, x /= m)) <$> coin)
                (\(m, r) -> if m == r then coin else pure m)
            game = B.Game (B.fromMonoidalLens optic)
            cached = B.cachePlay [False] [False, True] game
            contexts =
              [ B.Context ((,x) <$> coin) (\hidden y -> if hidden == y then coin else pure False)
              | x <- [False, True]
              ]
        expect
          "residual and hidden-state correlations"
          [B.runStrategy s c | s <- B.strategies game, c <- contexts]
          [B.runStrategy s c | s <- B.strategies cached, c <- contexts]
    , testProperty "cached play retains pure backward arrows and residual correlations" $ do
        let optic :: MonoidalLens (KL Bool :: B.Stochastic) (KL Bool) (KL Bool) (KL Bool)
            optic =
              monLens @(KL Bool)
                (B.Stochastic (\x -> Prelude ((\m -> (m, x /= m)) <$> coin)))
                (arr (uncurry (/=)))
            cachedOptic = B.cacheLens [False] [False, True] optic
            game = B.Game (B.fromMonoidalLens optic)
            cached = B.Game (B.fromMonoidalLens cachedOptic)
            contexts =
              [ B.Context ((,x) <$> coin) (\hidden y -> pure (hidden /= y))
              | x <- [False, True]
              ]
        withMonLens cachedOptic \_ _ backward -> case backward of
          Kleisli (Pure _) -> pure ()
          _ -> check "cached backward arrow became effectful" False
        expect
          "joint returns for cached and uncached inputs"
          [B.runStrategy s c | s <- B.strategies game, c <- contexts]
          [B.runStrategy s c | s <- B.strategies cached, c <- contexts]
    , testProperty "composed stochastic lenses support the standard getter" $ do
        let biased = either (error . show) id (weighted [(False, 1), (True, 3)])
            source :: MonoidalLens (KL () :: B.Stochastic) (KL Bool) (KL Bool) (KL Bool)
            source = B.behaviour (\() -> (\b -> (b, b)) <$> biased) (\(b, r) -> pure (b == r))
            negateOutput :: MonoidalLens (KL Bool :: B.Stochastic) (KL Bool) (KL Bool) (KL Bool)
            negateOutput = B.behaviour (\b -> pure ((), not b)) (\((), r) -> pure r)
        case view (source . negateOutput) of
          B.Stochastic forward ->
            expect
              "getter marginal of the composite"
              [(False, 3 / 4), (True, 1 / 4)]
              (probabilities (unPrelude (forward ())))
    , testProperty "pure primitives reproduce the deterministic game's full reports" $ do
        let c = B.context () (const ())
            deterministicReports =
              sort
                [ ([(outputs s (), 1)], evaluateStrategy s (Context () (const ())))
                | s <- strategies deterministicPD
                ]
            probabilisticReports =
              sort
                [(probabilities (B.outputs s (pure ())), B.evaluateStrategy s c) | s <- B.strategies purePD]
        expect "pure-game agreement" deterministicReports probabilisticReports
    , testProperty "impossible observations produce no diagnostic" $ do
        let g = B.decide "Player" [False, True] [False, True]
            c = B.stochasticContext (pure True) (\y -> pure (if y then 1 else 0))
            reports = [B.evaluateStrategy s c | s <- B.strategies g]
        check "unreached observation was evaluated" (all ((== ["True"]) . map B.observation) reports)
        expect "no NaN or division by zero" [[1], [1], [1], [1]] (map (map B.optimalPayoff) reports)
    , testProperty "hidden state need not have Eq, Ord, or Show instances" $ do
        let g = B.choose "Player" [False, True]
            c = B.Context (pure (not, ())) (\hidden y -> pure (if hidden y then 1 else 0))
        expect
          "function-valued hidden state"
          [["False"]]
          [map B.chosenAction (B.evaluateStrategy s c) | s <- B.equilibria g c]
    , testProperty "splitting prior branches leaves Bayesian diagnostics unchanged" $ do
        let g = B.chooseMixed "Player" [False, True] [pure False, pure True, coin]
            p = either (error . show) id (weighted [((False, ()), 1), ((False, ()), 1), ((True, ()), 2)])
            q = (,()) <$> coin
            k z y = pure (if z == y then 1 else 0)
        expect
          "branch representation affected evaluation"
          [B.evaluateStrategy s (B.Context q k) | s <- B.strategies g]
          [B.evaluateStrategy s (B.Context p k) | s <- B.strategies g]
    , testProperty "selected mixed strategies can be stored and reevaluated" $ do
        let g = B.chooseMixed "Player" [False, True] [coin]
            solutions = B.equilibria g (B.context () (const 0))
        expect "selection" 1 (length solutions)
        expect "play" [coin] [B.outputs s (pure ()) | s <- solutions]
        expect
          "new context changes rationality"
          [False]
          [B.isEquilibrium (B.evaluateStrategy s (B.context () (\y -> if y then 1 else 0))) | s <- solutions]
    , testProperty "mixed mass outside the legal action domain is inadmissible" $ do
        let g = B.chooseMixed "Player" [False] [coin]
        check "illegal support accepted" (null (B.equilibria g (B.context () (const 1))))
    , testProperty "typed profiles accept rational mixtures outside the catalogue" $ do
        let g = B.mixedDecision "Player" [()] [False, True] [coin]
            custom = either (error . show) id (weighted [(False, 1), (True, 2)])
            reports = B.evaluate g (const custom) (B.context () (\y -> if y then 1 else 0))
        expect "custom expected utility" [2 / 3] (map B.payoff reports)
        expect "full pure deviation check" [1] (map B.optimalPayoff reports)
        check "suboptimal custom mixture accepted" (not (B.isEquilibrium reports))
    , testProperty "finish closes a mixed game and preserves diagnostics" $ do
        let g :: B.Game (B.G () ()) (B.G () ())
            g = toSMC @I \() -> SMC.do
              a <- B.chooseMixed "Player" [False, True] [coin]
              B.finish (const 4) -< a
            c = B.context () (const ())
        expect "closed payoff" [[4]] [map B.payoff (B.evaluateStrategy s c) | s <- B.equilibria g c]
    ]
