{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | Open games in a copy/discard category. Strategies are finite catalogues of
-- monoidal lenses; contexts retain the joint state of the environment.
--
-- The categorical laws identify games up to bijections of profiles preserving
-- play and evaluation, with diagnostic lists compared up to permutation.
-- Enumeration order and diagnostic order are not categorical invariants.
-- Strictification handles profile parenthesisation, not arbitrary equivalence
-- of strategies. There is no 'Eq' instance for games containing opaque arrows.
module Proarrow.Category.Instance.OpenGame where

import Data.Kind (Type)
import Prelude (Bool, Eq, Ord, Rational, Show, String, ($), type (~))
import Prelude qualified as P

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  )
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Strictified (Fold, IsList (withIsList2), Strictified (..), concatFold, splitFold)
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Object (pattern Objs, type (++))
import Proarrow.Optic (iso)
import Proarrow.Optic.Getter (view)
import Proarrow.Optic.MonoidalLens (MonoidalLens, monLens, withMonLens)
import Proarrow.Tools.SMC (SYN (..), lift, toSMC, (-<))
import Proarrow.Tools.SMC qualified as SMC

type data GAME k = G k k

type Observation :: GAME k -> k
type family Observation a where
  Observation (G x s) = x

type Coutility :: GAME k -> k
type family Coutility a where
  Coutility (G x s) = s

-- | A joint state and a continuation sharing a hidden environment object.
-- A player's policy only sees the observation, never the hidden object. Arrows
-- remain lazy so components without checks need not build transported diagrams.
data Context (a :: GAME k) (b :: GAME k) where
  Context
    :: forall {k} {a :: GAME k} {b} z
     . (Ob z) => ~(Unit ~> z ** Observation a) -> ~(z ** Observation b ~> Coutility b) -> Context a b

-- | Exact utilities used by the finite decision primitives.
type Payoff = Rational

-- | A local best-response check, including all tied optimal actions.
data Diagnostic = Diagnostic
  { player :: String
  , observation :: String
  , chosenAction :: String
  , payoff :: Payoff
  , optimalActions :: [String]
  , optimalPayoff :: Payoff
  , equilibrium :: Bool
  }
  deriving (Eq, Ord, Show)

isEquilibrium :: [Diagnostic] -> Bool
isEquilibrium = P.all equilibrium

-- | A game with an explicit finite, lazy profile catalogue. Custom constructors
-- should supply each admissible profile once; enumeration can be exponential.
-- Profiles use 'Fold' of a strictified strategy list, so composing games
-- concatenates their lists without introducing parenthesisation into profiles.
data OpenGame (ss :: [Type]) (a :: GAME k) (b :: GAME k) where
  OpenGame
    :: (Ob ss, Ob a, Ob b)
    => { profiles :: [Fold ss]
       , play :: Fold ss -> MonoidalLens (Observation a) (Coutility a) (Observation b) (Coutility b)
       , evaluate :: Fold ss -> Context a b -> [Diagnostic]
       }
    -> OpenGame ss a b

-- | Hide the strategy list to obtain arrows of 'GAME'. Use 'strategies' to
-- access profiles with their play and evaluators, or 'withGame' for typed access.
type Game :: CAT (GAME k)
data Game a b where
  Game :: OpenGame ss a b -> Game a b

-- | A profile closed over its game's play and evaluator. It can be stored and
-- evaluated in different contexts without exposing the hidden profile type.
data Strategy (a :: GAME k) (b :: GAME k) where
  Strategy
    :: (Ob a, Ob b)
    => { playStrategy :: ~(MonoidalLens (Observation a) (Coutility a) (Observation b) (Coutility b))
       , evaluateStrategy :: Context a b -> [Diagnostic]
       }
    -> Strategy a b

-- | Enumerate profiles with their play and evaluator closed over the game.
strategies :: Game a b -> [Strategy a b]
strategies (Game g@OpenGame{}) = [Strategy (play g s) (evaluate g s) | s <- profiles g]

-- | Share each profile's play and evaluator closures across repeated uses.
-- The lazy catalogue retains its order and multiplicity; its hidden profile
-- representation becomes the corresponding first-class 'Strategy'.
memoisePlay :: forall k (a :: GAME k) b. Game a b -> Game a b
memoisePlay game@(Game OpenGame{}) =
  Game (OpenGame @'[Strategy a b] (strategies game) playStrategy evaluateStrategy)

-- | Equilibria within the supplied finite strategy catalogue.
equilibria :: Game a b -> Context a b -> [Strategy a b]
equilibria g c = P.filter (\s -> isEquilibrium (evaluateStrategy s c)) (strategies g)

withGame :: Game a b -> (forall ss. OpenGame ss a b -> r) -> r
withGame (Game g) k = k g

outputs :: (CopyDiscard k) => Strategy (a :: GAME k) b -> Observation a ~> Observation b
outputs s = view (playStrategy s)

-- | Execute both passes with the same residual, retaining joint outcomes.
runStrategy
  :: forall k (a :: GAME k) b. (CopyDiscard k) => Strategy a b -> Context a b -> Unit ~> Observation b ** Coutility a
runStrategy s@Strategy{} (Context @z prior continuation) =
  withMonLens (playStrategy s) \ @m _ forward backward ->
    ( toSMC @(F z :** F (Observation a)) \(hidden, input) -> SMC.do
        (residual, output) <- lift @_ @(F m :** F (Observation b)) forward input
        returned <- continuation -< (hidden, output)
        result <- backward -< (residual, returned)
        (output, result)
    )
      . prior

instance (CopyDiscard k) => CategoryOf (GAME k) where
  type (~>) = Game
  type Ob a = (a ~ G (Observation a) (Coutility a), Ob (Observation a), Ob (Coutility a))

instance (CopyDiscard k) => Profunctor (Game :: CAT (GAME k)) where
  dimap = dimapDefault
  r \\ Game OpenGame{} = r

instance (CopyDiscard k) => Promonad (Game :: CAT (GAME k)) where
  id = Game (fromArrows id id)
  Game h . Game g = Game (andThen g h)

-- | A nonstrategic component with one empty profile and no decision checks.
fromMonoidalLens
  :: (CopyDiscard k) => MonoidalLens (x :: k) s y r -> OpenGame '[] (G x s) (G y r)
fromMonoidalLens optic@Objs = OpenGame [()] (P.const optic) (\_ _ -> [])

fromArrows :: (CopyDiscard k) => (x :: k) ~> y -> r ~> s -> OpenGame '[] (G x s) (G y r)
fromArrows f g = fromMonoidalLens (iso f g)

-- | Transport a continuation through a downstream lens's forward and backward
-- legs. The residual from the forward pass is shared with the backward pass.
upstreamContinuation
  :: forall k (z :: k) m x y r s
   . (CopyDiscard k, Ob z, Ob m, Ob x, Ob y, Ob r, Ob s)
  => (x ~> m ** y) -> (z ** y ~> r) -> (m ** r ~> s) -> z ** x ~> s
upstreamContinuation forward continuation backward =
  toSMC @(F z :** F x) \(hidden, input) -> SMC.do
    (residual, output) <- lift @_ @(F m :** F y) forward input
    returned <- continuation -< (hidden, output)
    backward -< (residual, returned)

-- | Sequential play, transporting upstream deviations through the downstream lens.
andThen
  :: forall k ss ts (a :: GAME k) b c. (CopyDiscard k) => OpenGame ss a b -> OpenGame ts b c -> OpenGame (ss ++ ts) a c
andThen g@OpenGame{} h@OpenGame{} =
  withIsList2 @ss @ts $
    OpenGame
      [concatFold @ss @ts (s, t) | s <- profiles g, t <- profiles h]
      (\st -> let (s, t) = splitFold @ss @ts st in play g s . play h t)
      ( \st (Context @z prior continuation) ->
          let (s, t) = splitFold @ss @ts st
              upstream =
                withMonLens (play h t) \ @m _ forward backward ->
                  upstreamContinuation @k @z @m @(Observation b) @(Observation c) @(Coutility c) @(Coutility b)
                    forward
                    continuation
                    backward
              downstream =
                ( toSMC @(F z :** F (Observation a)) \(hidden, input) -> SMC.do
                    output <- view (play g s) -< input
                    (hidden, output)
                )
                  . prior
          in evaluate g s (Context @z prior upstream)
               P.++ evaluate h t (Context @z downstream continuation)
      )

-- | Independent parallel play; each deviation holds the other strategy fixed.
parallel
  :: forall k ss ts (a :: GAME k) b c d
   . (CopyDiscard k) => OpenGame ss a b -> OpenGame ts c d -> OpenGame (ss ++ ts) (a ** c) (b ** d)
parallel g@OpenGame{} h@OpenGame{} =
  withIsList2 @ss @ts $
    withOb2 @(GAME k) @a @c $
      withOb2 @(GAME k) @b @d $
        OpenGame
          [concatFold @ss @ts (s, t) | s <- profiles g, t <- profiles h]
          ( \st ->
              let (s, t) = splitFold @ss @ts st
              in withMonLens (play g s) \ @m _ v u -> withMonLens (play h t) \ @n _ w z ->
                   withOb2 @k @m @n $
                     monLens @(m ** n)
                       ( toSMC @(F (Observation a) :** F (Observation c)) \(x, x') -> SMC.do
                           (m, y) <- lift @_ @(F m :** F (Observation b)) v x
                           (n, y') <- lift @_ @(F n :** F (Observation d)) w x'
                           ((m, n), (y, y'))
                       )
                       ( toSMC @((F m :** F n) :** (F (Coutility b) :** F (Coutility d))) \((m, n), (r, r')) -> SMC.do
                           returned <- u -< (m, r)
                           returned' <- z -< (n, r')
                           (returned, returned')
                       )
          )
          ( \st (Context @z prior continuation) ->
              let (s, t) = splitFold @ss @ts st
                  v = view (play g s)
                  w = view (play h t)
                  leftPrior =
                    ( toSMC @(F z :** (F (Observation a) :** F (Observation c))) \(hidden, (x, x')) ->
                        (hidden, x', x)
                    )
                      . prior
                  rightPrior =
                    ( toSMC @(F z :** (F (Observation a) :** F (Observation c))) \(hidden, (x, x')) ->
                        (hidden, x, x')
                    )
                      . prior
                  leftK = toSMC @((F z :** F (Observation c)) :** F (Observation b)) \((hidden, x'), y) -> SMC.do
                    y' <- w -< x'
                    (r, _) <- lift @_ @(F (Coutility b) :** F (Coutility d)) continuation (hidden, (y, y'))
                    r
                  rightK = toSMC @((F z :** F (Observation a)) :** F (Observation d)) \((hidden, x), y') -> SMC.do
                    y <- v -< x
                    (_, r') <- lift @_ @(F (Coutility b) :** F (Coutility d)) continuation (hidden, (y, y'))
                    r'
              in withOb2 @k @z @(Observation c) $
                   withOb2 @k @z @(Observation a) $
                     evaluate g s (Context @(z ** Observation c) leftPrior leftK)
                       P.++ evaluate h t (Context @(z ** Observation a) rightPrior rightK)
          )

reindex :: [Fold ss] -> Strictified ss ts -> OpenGame ts a b -> OpenGame ss a b
reindex ss (Str f) g@OpenGame{} = OpenGame ss (play g P.. f) (evaluate g P.. f)

instance (CopyDiscard k) => MonoidalProfunctor (Game :: CAT (GAME k)) where
  one = id
  Game g ** Game h = Game (parallel g h)

instance (CopyDiscard k) => Monoidal (GAME k) where
  type Unit = G Unit Unit
  type a ** b = G (Observation a ** Observation b) (Coutility a ** Coutility b)
  withOb2 @a @b r = withOb2 @k @(Observation a) @(Observation b) (withOb2 @k @(Coutility a) @(Coutility b) r)
  leftUnitor @a = Game (fromArrows (leftUnitor @k @(Observation a)) (leftUnitorInv @k @(Coutility a)))
  leftUnitorInv @a = Game (fromArrows (leftUnitorInv @k @(Observation a)) (leftUnitor @k @(Coutility a)))
  rightUnitor @a = Game (fromArrows (rightUnitor @k @(Observation a)) (rightUnitorInv @k @(Coutility a)))
  rightUnitorInv @a = Game (fromArrows (rightUnitorInv @k @(Observation a)) (rightUnitor @k @(Coutility a)))
  associator @a @b @c =
    Game
      ( fromArrows
          (associator @k @(Observation a) @(Observation b) @(Observation c))
          (associatorInv @k @(Coutility a) @(Coutility b) @(Coutility c))
      )
  associatorInv @a @b @c =
    Game
      ( fromArrows
          (associatorInv @k @(Observation a) @(Observation b) @(Observation c))
          (associator @k @(Coutility a) @(Coutility b) @(Coutility c))
      )

instance (CopyDiscard k) => SymMonoidal (GAME k) where
  swap @a @b = Game (fromArrows (swap @k @(Observation a) @(Observation b)) (swap @k @(Coutility b) @(Coutility a)))
