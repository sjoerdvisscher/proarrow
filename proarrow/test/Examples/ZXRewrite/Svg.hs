-- | Draw the ZX cleanup rules with the law gallery's SVG equation layout.
module Examples.ZXRewrite.Svg (ruleSvgs) where

import Data.Containers.ListUtils (nubOrd)
import Data.IntMap.Strict qualified as IM
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Prelude hiding ((.))

import Examples.ZXRewrite.Diagram
  ( Colour (..)
  , Generator (..)
  , ports
  , sorts
  )
import Examples.ZXRewrite.Pictures (phaseLabel)
import Examples.ZXRewrite.Rules (PhaseSum (..), colourChangeRule, learnedSymbolicCleanupRules, phaseVariable)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Monoidal.Strictified (Fold, Strictified (..), withIsListOf, withObFold)
import Proarrow.Core (CategoryOf (..), Promonad (..), UN)
import Proarrow.Object (ListOf (..), SomeOf (..), withKnownListOf)
import Proarrow.Tools.Diagrams.Svg qualified as Svg
import Proarrow.Tools.HypergraphRewrite qualified as R

type Q = Svg.S '[Svg.Wire ""]

-- | One SVG per fixed cleanup rule, followed by colour change at arity three.
-- A boundary label ending in an ellipsis stands for a sequence of legs.
ruleSvgs :: Either String [(String, String)]
ruleSvgs = do
  rules <- learnedSymbolicCleanupRules
  fixed <- traverse drawRule rules
  colour <- colourExample
  pure (fixed ++ [("Colour change (three legs)", colour)])
  where
    drawRule (name, rule) = do
      (left, right) <- R.parameterPortExample variable rule
      svg <- drawEquation left right
      pure (name, svg)
    variable "alpha" = phaseVariable 0
    variable _ = phaseVariable 1

colourExample :: Either String String
colourExample = do
  rule <- colourChangeRule
  let boundary = [0, 1, 2]
      source = HG.unsafeOpenHypergraph @_ @HG.W3 @'[] (sorts 3) boundary [] [HG.Box (Spider X (phaseVariable 0)) [] boundary]
      fragment graph =
        let (ns, ins, _, boxes) = HG.hypergraphParts graph
        in R.PortGraph ns ins (map (fmap R.Node) boxes)
  case R.rewrites rule source of
    [target] -> drawEquation (fragment source) (fragment target)
    _ -> Left "expected one colour-change example"

drawEquation :: R.PortGraph () (Generator PhaseSum) -> R.PortGraph () (Generator PhaseSum) -> Either String String
drawEquation left@(R.PortGraph _ boundary boxes) right =
  withWires (length names) \ @as wires -> withKnownListOf wires do
    l <- side @as left
    r <- side @as right
    pure
      (Svg.sideBySideWithBoundary options [] [(name, Svg.Plain) | name <- names] (map (drawing . unStr) [l, r]))
  where
    options = Svg.defaultOptions{Svg.bendSpiders = True, Svg.slidePoints = True}
    drawing :: Svg.Svg a b -> Svg.Diagram
    drawing (Svg.Svg _ d) = d
    sequences = nubOrd [name | box <- boxes, R.Capture name <- ports box]
    names = ["q" ++ show i | i <- [1 .. length boundary]] ++ map (++ "…") sequences
    markers = Map.fromList (zip sequences [0 ..])
    side :: forall as. (HG.SortList as) => R.PortGraph () (Generator PhaseSum) -> Either String (('[] :: [Svg.SVG]) ~> as)
    side (R.PortGraph ns interface bs) = do
      let n = length ns
          wire (R.Node i) = Right i
          wire (R.Capture name) = maybe (Left ("unknown capture " ++ name)) (Right . (n +)) (Map.lookup name markers)
          wire R.Element{} = Left "instantiate individual capture elements before drawing"
          box b = do
            legs <- traverse wire (ports b)
            pure (HG.Box (boxName (HG.label b), length legs) [] legs)
      concrete <- traverse box bs
      graph <-
        HG.openHypergraph @_ @'[] @as
          (replicate (n + length sequences) qubit)
          []
          (interface ++ [n .. n + length sequences - 1])
          concrete
      HG.readBack HG.frobenius (uncurry drawBox) graph

qubit :: HG.SomeSort Svg.SVG
qubit = Some @Q

withWires :: Int -> (forall (as :: [Svg.SVG]). HG.Sorts as -> r) -> r
withWires 0 k = k Nil
withWires n k = withWires (n - 1) (\ws -> k (Cons @Q ws))

drawBox :: String -> Int -> HG.SomeArrow Svg.SVG
drawBox name n = withWires n \ @bs ws ->
  withIsListOf ws $
    HG.SomeArrow Nil ws (Str (withObFold @bs (Svg.node @'[Svg.I] @(UN Svg.S (Fold bs)) name)))

boxName :: Generator PhaseSum -> String
boxName Hadamard = "H"
boxName (Spider c p) = show c ++ "(" ++ showPhase p ++ ")"
boxName (Scalar power angle) = "√2^" ++ show power ++ phaseLabel angle
boxName (Selected p) = "Z(" ++ showPhase p ++ ")"
boxName (Pivot _ p) = "Z(" ++ showPhase p ++ ")"

showPhase :: PhaseSum -> String
showPhase (PhaseSum offset terms) = case variables ++ [phaseLabel offset | offset /= 0] of
  [] -> "0"
  xs -> intercalate " + " xs
  where
    variables = [coefficient n ++ if i == 0 then "α" else "β" | (i, n) <- IM.toAscList terms]
    coefficient 1 = ""
    coefficient n = show n
