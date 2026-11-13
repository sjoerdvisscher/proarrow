{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QualifiedDo #-}

-- | A seller chooses a reserve, then two bidders privately observe their values.
-- Bids do not observe the reserve, as in the upstream reserve-price example.
-- Each supplied policy gives one catalogue entry; deviations still check every
-- legal action. No enumeration of all valuation-to-bid functions is needed.
module Examples.OpenGames.Auction
  ( Amount (..)
  , amounts
  , amount
  , Rule (..)
  , Bidder (..)
  , Outcome (..)
  , Policy
  , truthful
  , independentValues
  , settle
  , bidderUtility
  , sellerRevenue
  , auction
  , bidding
  , reports
  , outcomes
  , Components (..)
  , auctionWith
  , rawComponents
  , test
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (for_)
import Data.List (sort, sortOn)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Lazy qualified as M
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Examples.OpenGames.Bayesian
import Examples.OpenGames.Probability
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), arr)
import Proarrow.Category.Instance.OpenGame qualified as OG
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (Promonad (..))
import Proarrow.Functor qualified as PF
import Proarrow.Optic.MonoidalLens (MonoidalLens, monLens)
import Proarrow.Testing (check, expect)
import Proarrow.Tools.SMC (SYN (..), lift, toSMC, (-<))
import Proarrow.Tools.SMC qualified as SMC

data Amount = A0 | A20 | A40 | A60 | A80 | A100 deriving (Eq, Ord, Enum, Bounded)

instance Show Amount where
  show = show . (20 *) . fromEnum

amounts :: NonEmpty Amount
amounts = [A0, A20, A40, A60, A80, A100]

amount :: Amount -> Payoff
amount = fromIntegral . (20 *) . fromEnum

data Rule = FirstPrice | SecondPrice deriving (Eq, Show)
data Bidder = Alice | Bob deriving (Eq, Ord, Show)
data Outcome = NoSale | Sold Bidder Amount deriving (Eq, Ord, Show)

type Policy = Amount -> Distribution Amount

truthful :: Policy
truthful = pure

independentValues :: Distribution (Amount, Amount)
independentValues = (,) <$> uniform amounts <*> uniform amounts

-- | Equal highest bids split the allocation probability, including zero-price
-- ties. The winner pays its bid or the greater of the reserve and the other bid.
settle :: Rule -> Amount -> (Amount, Amount) -> Distribution Outcome
settle rule reserve (a, b)
  | max a b < reserve = pure NoSale
  | a > b = pure (Sold Alice price)
  | b > a = pure (Sold Bob price)
  | otherwise = uniform [Sold Alice price, Sold Bob price]
  where
    price = case rule of
      FirstPrice -> max a b
      SecondPrice -> max reserve (min a b)

bidderUtility :: Bidder -> Amount -> Outcome -> Payoff
bidderUtility who value (Sold winner payment)
  | who == winner = amount value - amount payment
bidderUtility _ _ _ = 0

sellerRevenue :: Outcome -> Payoff
sellerRevenue NoSale = 0
sellerRevenue (Sold _ payment) = amount payment

selected :: forall policy {k} (a :: OG.GAME k) b. policy -> OG.OpenGame '[policy] a b -> OG.Game a b
selected policy g = OG.Game (OG.reindex [policy] (id :: Strictified '[policy] '[policy]) g)

-- Components keep the cache boundary replaceable for comparison with the
-- original composed evaluator. A cache hook replaces both play and diagnostics.
data Components = Components
  { sellerChoice :: Amount -> Game (G () ()) (G Amount Payoff)
  , bidderChoice :: String -> Policy -> Game (G Amount ()) (G Amount Payoff)
  , bidderReturn :: Bidder -> Game (G (Amount, Amount) ((), Payoff)) (G Amount Outcome)
  , valuePrior :: Game (G () ()) (G (Amount, Amount) ((), ()))
  , settleGame :: Game (G ((Amount, Amount), Amount) ((Payoff, Outcome), Outcome)) (G Outcome ())
  , cacheBidder :: Game (G Amount ()) (G Amount Outcome) -> Game (G Amount ()) (G Amount Outcome)
  , cacheBidding :: Policy -> Policy -> Game (G Amount Payoff) (G Outcome ()) -> Game (G Amount Payoff) (G Outcome ())
  }

bidderWith :: Components -> Bidder -> Policy -> Game (G Amount ()) (G Amount Outcome)
bidderWith c who policy = cacheBidder c $ toSMC @(F (G Amount ())) \value -> SMC.do
  (retained, seen) <-
    lift @(F (G Amount ())) @(F (G Amount ()) :** F (G Amount ()))
      (Game (fromFunctions (\x -> (x, x)) (const ())))
      value
  bid <- bidderChoice c (show who) policy -< seen
  bidderReturn c who -< (retained, bid)

biddingWith :: Components -> Policy -> Policy -> Game (G Amount Payoff) (G Outcome ())
biddingWith c alice bob = cacheBidding c alice bob $ toSMC @(F (G Amount Payoff)) \reserve -> SMC.do
  (va, vb) <- lift @I @(F (G Amount ()) :** F (G Amount ())) (valuePrior c) SMC.unit
  a <- bidderWith c Alice alice -< va
  b <- bidderWith c Bob bob -< vb
  settleGame c -< (reserve, a, b)

auctionWith :: Components -> Amount -> Policy -> Policy -> Game (G () ()) (G Outcome ())
auctionWith c reserve alice bob = unStr $ toSMC @I \() -> SMC.do
  r <- Str @'[] @'[G Amount Payoff] (sellerChoice c reserve)
  Str @'[G Amount Payoff] @'[G Outcome ()] (biddingWith c alice bob) -< r

returns :: NonEmpty Outcome
returns = [NoSale] <> (Sold Alice <$> amounts) <> (Sold Bob <$> amounts)

rawComponents :: Rule -> Distribution (Amount, Amount) -> Components
rawComponents rule prior =
  Components
    { sellerChoice = \reserve -> selected (const (pure reserve)) (decision "Seller" [()] amounts)
    , bidderChoice = \name policy -> selected policy (decision name amounts amounts)
    , bidderReturn = \who -> Game (fromMonoidalLens (behaviour pure (\(v, outcome) -> pure ((), bidderUtility who v outcome))))
    , valuePrior = Game (fromFunctions id (const ())) . nature prior
    , settleGame = settlement rule
    , cacheBidder = cachePlay amounts returns
    , cacheBidding = cachedBidding rule prior
    }

-- The finite cache replaces play and diagnostics for a selected profile.
-- Multiple-profile catalogues retain the original bidding body.
cacheSelectedBidding
  :: forall k (a :: OG.GAME k) b
   . MonoidalLens (OG.Observation a) (OG.Coutility a) (OG.Observation b) (OG.Coutility b)
  -> (OG.Context a b -> [Diagnostic])
  -> OG.Game a b
  -> OG.Game a b
cacheSelectedBidding optic checkBidders game@(OG.Game (g@OG.OpenGame{} :: OG.OpenGame ss a b)) =
  case OG.profiles g of
    [_] ->
      OG.memoisePlay
        ( OG.Game
            ( OG.OpenGame @ss
                (OG.profiles g)
                (const optic)
                (\_ ctx -> checkBidders ctx)
            )
        )
    _ -> game

-- Seller and both bidders share policy weights and settlement cells. Each
-- bidder retains the correlation between their valuation and the opponent bid.
cachedBidding
  :: Rule
  -> Distribution (Amount, Amount)
  -> Policy
  -> Policy
  -> Game (G Amount Payoff) (G Outcome ())
  -> Game (G Amount Payoff) (G Outcome ())
cachedBidding rule prior alice bob = cacheSelectedBidding seller $ \ctx ->
  let reserves = reservePrior ctx
  in checkBidder Alice alice reserves ++ checkBidder Bob bob reserves
  where
    domain = NE.toList amounts
    policyTable policy = M.fromList [(v, weightedValues (policy v)) | v <- domain]
    alicePolicy = policyTable alice
    bobPolicy = policyTable bob
    opponentMarginal own other policy =
      M.fromListWith
        (+)
        [ ((own pair, bid), p * q)
        | (pair, p) <- weightedValues prior
        , (bid, q) <- policy M.! other pair
        ]
    aliceOpponentBids = opponentMarginal fst snd bobPolicy
    bobOpponentBids = opponentMarginal snd fst alicePolicy
    jointBids =
      M.toAscList
        ( M.fromListWith
            (+)
            [ ((a, b), p * q)
            | ((va, b), p) <- M.toAscList aliceOpponentBids
            , (a, q) <- alicePolicy M.! va
            ]
        )
    settlements =
      M.fromList
        [ ((reserve, a, b), weightedValues (settle rule reserve (a, b)))
        | reserve <- domain
        , a <- domain
        , b <- domain
        ]
    kernel reserve =
      either
        (error . show)
        id
        ( weighted
            [ ((outcome, outcome), p)
            | (outcome, p) <-
                M.toAscList
                  ( M.fromListWith
                      (+)
                      [ (outcome, p * q)
                      | ((a, b), p) <- jointBids
                      , (outcome, q) <- settlements M.! (reserve, a, b)
                      ]
                  )
            ]
        )
    kernels = M.fromList [(reserve, kernel reserve) | reserve <- domain]
    seller =
      monLens @(KL Outcome)
        (Stochastic (PF.Prelude . (\reserve -> kernels M.! reserve)))
        (arr (\(outcome, ()) -> sellerRevenue outcome))
    checkBidder who policy =
      let ownValue = case who of Alice -> fst; Bob -> snd
          opponents = case who of Alice -> aliceOpponentBids; Bob -> bobOpponentBids
          values = nubOrd [ownValue pair | (pair, _) <- weightedValues prior]
          masses = M.fromListWith (+) [(ownValue pair, p) | (pair, p) <- weightedValues prior]
          ownPrior =
            either
              (error . show)
              id
              ( weighted
                  [((value, value), masses M.! value) | value <- values]
              )
          outcomesFor reserve bid otherBid =
            settlements M.! case who of
              Alice -> (reserve, bid, otherBid)
              Bob -> (reserve, otherBid, bid)
      in \reserves ->
           let scores =
                 M.fromList
                   [ ( (value, bid)
                     , sum
                         [ pReserve * pOpponent * pOutcome * bidderUtility who value outcome
                         | (reserve, pReserve) <- weightedValues reserves
                         , otherBid <- domain
                         , let pOpponent = M.findWithDefault 0 (value, otherBid) opponents
                         , pOpponent > 0
                         , (outcome, pOutcome) <- outcomesFor reserve bid otherBid
                         ]
                         / (masses M.! value)
                     )
                   | value <- values
                   , bid <- domain
                   ]
           in evaluate
                (decision (show who) amounts amounts)
                policy
                (Context ownPrior (\value bid -> pure (scores M.! (value, bid))))

reservePrior :: Context (G Amount Payoff) (G Outcome ()) -> Distribution Amount
reservePrior (OG.Context prior _) = case prior of
  Stochastic forward -> collect (snd <$> PF.unPrelude (forward ()))

-- | One sampled settlement is the forward output and the backward return to
-- both bidders. The seller receives its revenue from that same outcome.
settlement :: Rule -> Game (G ((Amount, Amount), Amount) ((Payoff, Outcome), Outcome)) (G Outcome ())
settlement rule = Game (fromMonoidalLens (behaviour forward backward))
  where
    forward ((reserve, a), b) = (\outcome -> (outcome, outcome)) <$> settle rule reserve (a, b)
    backward (outcome, ()) = pure ((sellerRevenue outcome, outcome), outcome)

bidding
  :: Rule -> Distribution (Amount, Amount) -> Policy -> Policy -> Game (G Amount Payoff) (G Outcome ())
bidding rule prior = biddingWith (rawComponents rule prior)

-- | Check selected bidder policies and a reserve against all local deviations.
auction :: Rule -> Distribution (Amount, Amount) -> Amount -> Policy -> Policy -> Game (G () ()) (G Outcome ())
auction rule prior = auctionWith (rawComponents rule prior)

reports :: Rule -> Distribution (Amount, Amount) -> Amount -> Policy -> Policy -> [Diagnostic]
reports rule prior reserve alice bob = gameReports (auction rule prior reserve alice bob)

gameReports :: Game (G () ()) (G Outcome ()) -> [Diagnostic]
gameReports game = concat [evaluateStrategy s (context () (const ())) | s <- strategies game]

outcomes :: Rule -> Distribution (Amount, Amount) -> Amount -> Policy -> Policy -> Distribution Outcome
outcomes rule prior reserve alice bob =
  case strategies (auction rule prior reserve alice bob) of
    [s] -> outputs s (pure ())
    _ -> error "auction: expected one selected profile"

shaded :: Policy
shaded value = pure (toEnum (max 0 (fromEnum value - 1)))

mixed :: Policy
mixed value = uniform [value, toEnum (max 0 (fromEnum value - 1))]

correlated :: Distribution (Amount, Amount)
correlated = either (error . show) id (weighted [((A20, A100), 1), ((A100, A20), 2)])

originalAuction :: Rule -> Distribution (Amount, Amount) -> Amount -> Policy -> Policy -> Game (G () ()) (G Outcome ())
originalAuction rule prior =
  auctionWith
    ((rawComponents rule prior){cacheBidding = \_ _ game -> cachePlay amounts [()] game})

diagnostics :: Game (G () ()) (G Outcome ()) -> [Diagnostic]
diagnostics = sortOn (\d -> (player d, observation d)) . gameReports

test :: TestTree
test =
  testGroup
    "Auctions"
    [ testProperty "selected policies avoid enumerating the full six-value bidding space" $ do
        let g = auction SecondPrice independentValues A60 truthful truthful
        expect "selected catalogue" 1 (length (strategies g))
        expect
          "seller and both bidders at all six valuations"
          13
          (length (reports SecondPrice independentValues A60 truthful truthful))
    , testProperty "truthful second-price bidding and reserve 60 form an equilibrium" $ do
        let ds = reports SecondPrice independentValues A60 truthful truthful
        check "profitable deviation" (isEquilibrium ds)
        expect "seller revenue" [430 / 9] [payoff d | d <- ds, player d == "Seller"]
        expect "best reserve" [["60"]] [optimalActions d | d <- ds, player d == "Seller"]
    , testProperty "changing to first price gives truthful bidders profitable deviations" $ do
        let ds = reports FirstPrice independentValues A0 truthful truthful
        check "first-price truthful bidding accepted" (any (\d -> player d /= "Seller" && not (equilibrium d)) ds)
    , testProperty "equal bids split the allocation and share the settlement with utilities" $ do
        let prior = pure (A80, A80)
        expect
          "fair allocation"
          [(Sold Alice A80, 1 / 2), (Sold Bob A80, 1 / 2)]
          (probabilities (outcomes SecondPrice prior A0 truthful truthful))
        expect
          "no profit when paying one's full value"
          [0, 0]
          [payoff d | d <- reports SecondPrice prior A0 truthful truthful, player d /= "Seller"]
    , testProperty "a reserve above all bids leaves the good unsold" $ do
        expect
          "unsold outcome"
          (pure NoSale)
          (outcomes SecondPrice (pure (A20, A20)) A40 truthful truthful)
    , testProperty "marginal caches preserve composed game evaluation" $ do
        for_ @[] [FirstPrice, SecondPrice] $ \rule ->
          for_ @[] [(independentValues, A60), (correlated, A40), (pure (A80, A80), A100)] $ \(prior, reserve) ->
            for_ @[] [(truthful, truthful), (shaded, truthful), (mixed, shaded)] $ \(alice, bob) -> do
              let original = originalAuction rule prior reserve alice bob
                  cached = auction rule prior reserve alice bob
              expect "all diagnostics" (diagnostics original) (diagnostics cached)
              expect
                "complete output distributions"
                [outputs s (pure ()) | s <- strategies original]
                [outcomes rule prior reserve alice bob]
    , testProperty "bidder marginal caches average an unobserved stochastic reserve" $ do
        for_ @[] [FirstPrice, SecondPrice] $ \rule -> do
          let choice = decision "Seller" [()] amounts
              seller =
                Game
                  ( OpenGame @'[() -> Distribution Amount]
                      [const (uniform [A0, A60])]
                      (play choice)
                      (evaluate choice)
                  )
              components = (rawComponents rule correlated){sellerChoice = const seller}
              original = components{cacheBidding = \_ _ game -> cachePlay amounts [()] game}
              ds c = diagnostics (auctionWith c A40 mixed shaded)
          expect "all diagnostics under a mixed reserve" (ds original) (ds components)
    , testProperty "marginal caches preserve every counterfactual payoff" $ do
        for_ @[] [FirstPrice, SecondPrice] $ \rule ->
          for_ @[] [Alice, Bob] $ \who -> do
            let utilities report =
                  sort
                    [ (observation d, show bid, payoff d)
                    | bid <- NE.toList amounts
                    , let (alice, bob) = if who == Alice then (const (pure bid), mixed) else (mixed, const (pure bid))
                    , d <- report alice bob
                    , player d == show who
                    ]
            expect
              "all reached observations and candidate bids"
              (utilities (\alice bob -> diagnostics (originalAuction rule correlated A40 alice bob)))
              (utilities (reports rule correlated A40))
    ]
