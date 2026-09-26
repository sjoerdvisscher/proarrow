{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | String diagrams rendered to Graphviz: 'Dot' is a monoidal category of diagram fragments
-- ('node', 'line', the adjunction unit and counit 'unitAdj'\/'counitAdj', ...) indexed by their typed input and
-- output wires, and 'run' emits the composed diagram as dot source ('runEquation' two of them as
-- an equation).
module Proarrow.Tools.Diagrams.Dot where

import Data.Bifunctor (first)
import Data.Char (digitToInt, isDigit)
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (..))
import Data.List qualified as List
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Prelude hiding (Monoid (..), curry, id, (.))

import Proarrow.Category.Instance.Free (All)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), Strictly (..), SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph
  ( ExpHG
  , Frobenius
  , Hypergraph
  , applyHG
  , curryHG
  , dualHG
  , linDistHG
  , linDistInvHG
  )
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strength (Costrong (..))
import Proarrow.Category.Monoidal.Strictified (IsList (..), SList (..), type (++))
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid (..), Monoid (..))
import Proarrow.Tools.Laws (Equation (..), Labelled (..), Law (..), Laws (..), lawName)

type Port = String -- Basically a shown int, but may contain an additional direction (:n, :e, :s, :w)

newtype Vec as x = Vec {unVec :: [x]}
  deriving newtype (Show, Eq, Foldable, Functor)
instance Traversable (Vec as) where
  traverse f (Vec xs) = fmap Vec (traverse f xs)
newtype Fin as = Fin {unFin :: Int}
  deriving newtype (Show, Eq, Num)
(!) :: Vec as x -> Fin as -> x
Vec xs ! Fin i = xs !! i

(+++) :: Vec as x -> Vec bs x -> Vec (as ++ bs) x
Vec xs +++ Vec ys = Vec (xs ++ ys)

split :: (IsList as) => Vec (as ++ bs) x -> (Vec as x, Vec bs x)
split @as (Vec xs) = case splitAt (len @as) xs of (as, bs) -> (Vec as, Vec bs)

len :: (IsList as) => Int
len @as = case sList @as of
  SNil -> 0
  SSing -> 1
  SCons @_ @bs -> 1 + len @bs

ixs :: (IsList as) => Vec as (Fin as)
ixs @as = case sList @as of
  SNil -> Vec []
  SSing -> Vec [0]
  SCons @_ @bs -> coerce (0 : fmap (+ 1) (unVec (ixs @bs)))

ixed :: (IsList as) => Vec as x -> Vec as (Fin as, x)
ixed (Vec []) = Vec []
ixed (Vec (x : xs)) = Vec $ (0, x) : fmap (\(i, y) -> (i + 1, y)) (unVec (ixed (Vec xs)))

zipV3 :: Vec as x -> Vec as y -> Vec as z -> Vec as (x, y, z)
zipV3 (Vec xs) (Vec ys) (Vec zs) = Vec (zip3 xs ys zs)

relax :: forall bs as. Fin as -> Fin (as ++ bs)
relax (Fin i) = Fin i

shift :: forall as bs. (IsList as) => Fin bs -> Fin (as ++ bs)
shift (Fin i) = Fin (len @as + i)

eitherF :: forall as bs r. (IsList as) => (Fin as -> r) -> (Fin bs -> r) -> Fin (as ++ bs) -> r
eitherF f g (Fin i)
  | i < len @as = f (Fin i)
  | otherwise = g (Fin (i - len @as))

names :: (IsList (as :: [Symbol])) => Vec as String
names @as = case sList @as of
  SNil -> Vec []
  SSing @s -> Vec [symbolVal (Proxy @s)]
  SCons @s @ss -> Vec (symbolVal (Proxy @s) : unVec (names @ss))

type SymRefl :: CAT Symbol
data SymRefl a b where
  SymRefl :: (KnownSymbol s) => SymRefl s s
instance Eq (SymRefl a b) where
  SymRefl == SymRefl = True
instance Show (SymRefl a b) where
  show SymRefl = "SymRefl"
instance Profunctor SymRefl where
  dimap = dimapDefault
  r \\ SymRefl = r
instance Promonad SymRefl where
  id = SymRefl
  SymRefl . SymRefl = SymRefl

-- | The discrete category on type-level 'Symbol's, labelling the wires of a string diagram.
instance CategoryOf Symbol where
  type (~>) = SymRefl
  type Ob s = KnownSymbol s

type DOT :: Kind
type data DOT = D [Symbol]

data DotData as bs = DotData
  { inputs :: Vec as (Either (Fin bs) Port)
  , outputs :: Vec bs (Either (Fin as) Port)
  , edges :: [(Port, String, Port)]
  , nodes :: [(NodeKind, String)]
  -- ^ what each node means, and its Graphviz options
  }
  deriving (Show, Eq)

-- | What a node means, as opposed to how it is drawn.
data NodeKind
  = -- | all its wires carry the same value: a (co)monoid point, a cup or a cap
    Spider
  | -- | 'swapNode'
    Crossing
  | -- | a generator, 'node'
    Box
  deriving (Show, Eq, Ord)

type Dot :: CAT DOT
data Dot a b where
  Dot :: (IsList as, IsList bs) => (Int -> (Int, DotData as bs)) -> Dot (D as) (D bs)

instance Show (Dot a b) where
  show (Dot f) = show (getData (Dot f))

instance Profunctor Dot where
  dimap = dimapDefault
  r \\ Dot{} = r
instance Promonad Dot where
  id @(D as) =
    Dot
      (,DotData
          { inputs = fmap Left (ixs @as)
          , outputs = fmap Left (ixs @as)
          , edges = []
          , nodes = []
          })
  Dot @bs l . Dot r = Dot \i ->
    let (k, DotData li lo le ln) = l j; (j, DotData ri ro re rn) = r i
    in ( k
       , DotData
           { inputs = fmap (either (li !) Right) ri
           , outputs = fmap (either (ro !) Right) lo
           , edges = re ++ foldMap (\case (Right n1, n, Right n2) -> [(n1, n, n2)]; _ -> []) (zipV3 ro (names @bs) li) ++ le
           , nodes = rn ++ ln
           }
       )

-- | The category string diagrams are built in: an object @'D' ws@ is the list of wire labels
-- along a boundary, and an arrow accumulates the Graphviz data connecting its input wires to its
-- output wires.
instance CategoryOf DOT where
  type (~>) = Dot
  type Ob a = (Is D a, IsList (UN D a))

instance MonoidalProfunctor Dot where
  one = Dot (,DotData (Vec []) (Vec []) [] [])
  Dot @lis @los l ** Dot @ris @ros r = withIsList2 @lis @ris $ withIsList2 @los @ros $ Dot \i ->
    let (j, DotData li lo le ln) = l i; (k, DotData ri ro re rn) = r j
    in ( k
       , DotData
           { inputs = fmap (first (relax @ros)) li +++ fmap (first (shift @los)) ri
           , outputs = fmap (first (relax @ris)) lo +++ fmap (first (shift @lis)) ro
           , edges = le ++ re
           , nodes = ln ++ rn
           }
       )
instance Monoidal DOT where
  type Unit = D '[]
  type ls ** rs = D (UN D ls ++ UN D rs)
  withOb2 @(D ls) @(D rs) r = withIsList2 @ls @rs r
  associator @as @bs @cs = associatorDefault @as @bs @cs
  associatorInv @as @bs @cs = associatorDefault @as @bs @cs
instance SymMonoidal DOT where
  swap @(D as) @(D bs) =
    withIsList2 @as @bs $
      withIsList2 @bs @as $
        Dot \n ->
          let as = ixs @as; bs = ixs @bs
          in ( n
             , DotData
                 { inputs = fmap Left (fmap (shift @bs) as +++ fmap (relax @as) bs)
                 , outputs = fmap Left (fmap (shift @as) bs +++ fmap (relax @bs) as)
                 , edges = []
                 , nodes = []
                 }
             )

-- | One point node for each wire of @as@. @inAt@ and @outAt@ say which wire's node each input and
-- output is attached to, and at which port. Drawing the (co)monoid on several wires as a single
-- point would not say which output continues which input.
pointsPerWire
  :: forall (as :: [Symbol]) xs ys
   . (IsList as, IsList xs, IsList ys)
  => (Fin xs -> (Int, String))
  -> (Fin ys -> (Int, String))
  -> String
  -> Dot (D xs) (D ys)
pointsPerWire inAt outAt opts = Dot \n ->
  let at :: forall zs ws. (Fin zs -> (Int, String)) -> Fin zs -> Either (Fin ws) Port
      at f i = let (w, port) = f i in Right (show (n + w) ++ port)
  in ( n + len @as
     , DotData
         { inputs = fmap (at inAt) (ixs @xs)
         , outputs = fmap (at outAt) (ixs @ys)
         , edges = []
         , nodes = replicate (len @as) (Spider, opts)
         }
     )

-- | Attaches at the given port of wire @i@'s point.
wireAt :: String -> Fin as -> (Int, String)
wireAt port (Fin i) = (i, port)

-- | Attaches wire @i@ of either copy in @as ++ as@ to wire @i@'s point, the first copy at the
-- first port and the second at the second.
eitherCopy :: forall (as :: [Symbol]). (IsList as) => String -> String -> Fin (as ++ as) -> (Int, String)
eitherCopy l r = eitherF @as @as (wireAt l) (wireAt r)

instance (Ob as) => Monoid (D as) where
  mempty = pointsPerWire @as (wireAt "") (wireAt ":s") "shape=point; width=0.07; fillcolor=white"
  mappend =
    withIsList2 @as @as $
      pointsPerWire @as (eitherCopy @as ":nw" ":ne") (wireAt ":s") "shape=point; width=0.07; fillcolor=white"
instance (Ob as) => Comonoid (D as) where
  counit = pointsPerWire @as (wireAt ":n") (wireAt "") "shape=point; width=0.07"
  comult =
    withIsList2 @as @as $
      pointsPerWire @as (wireAt ":n") (eitherCopy @as ":sw" ":se") "shape=point; width=0.07"
instance (Ob as) => CocommutativeComonoid (D as)
instance (Ob as) => CommutativeMonoid (D as)

-- | The points are spiders: on each wire, merging and copying are the special commutative
-- Frobenius structure.
instance (Ob as) => Frobenius (D as)

instance CopyDiscard DOT

-- | The points make every object a special commutative Frobenius object, so a diagram's wires can
-- be bent: each object is its own dual, with cups and caps drawn as a copy or merge point next to
-- a unit or counit point.
instance Hypergraph DOT

instance Closed DOT where
  type a ~~> b = ExpHG a b
  withObExp @a @b r = withOb2 @DOT @a @b r
  curry @a @b = curryHG @a @b
  apply @b @c = applyHG @b @c

instance StarAutonomous DOT where
  type Dual a = a
  withObDual r = r
  dual = dualHG
  dualInv = dualHG
  linDist @a @b @c = linDistHG @a @b @c
  linDistInv @a @b @c = linDistInvHG @a @b @c

instance CompactClosed DOT where
  distribDual @a @b = withOb2 @DOT @a @b id
  dualUnit = id
instance Costrong Tensor Dot where
  coact @(D as) @(D xs) @(D ys) (Dot f) = Dot \n ->
    case f n of
      (n', DotData is os es ns) ->
        let
          inps = fmap fromI is
          outs = fmap fromO os
          (ais, xs) = split @as @xs inps
          (aos, ys) = split @as @ys outs
          fromI = either (eitherF @as @ys (ais !) Left) Right
          fromO = either (eitherF @as @xs (aos !) Left) Right
        in
          ( n'
          , DotData
              { inputs = xs
              , outputs = ys
              , edges =
                  es
                    ++ foldMap (\case (Right n1, nm, Right n2) -> [feedback n1 nm n2]; _ -> []) (zipV3 aos (names @as) ais)
              , nodes = ns
              }
          )

-- | A fed-back wire. One that returns to the node it leaves is attached at corners of its ports, so
-- that Graphviz draws the loop beside the node and not across it; one between two nodes attaches
-- as any other wire does.
feedback :: Port -> String -> Port -> (Port, String, Port)
feedback from nm to
  | nodeOf from == nodeOf to = (bend ":sw" from, nm, bend ":nw" to)
  | otherwise = (from, nm, to)

-- | A port with the side it is drawn at replaced by the given corner.
bend :: String -> Port -> Port
bend corner p = case break (== ':') (reverse p) of
  (side, ':' : rest) | reverse side `elem` (["n", "ne", "e", "se", "s", "sw", "w", "nw", "c"] :: [String]) -> reverse rest ++ corner
  _ -> p ++ corner

swap2 :: (Ob a, Ob b) => Dot (D [a, b]) (D [b, a])
swap2 @a @b = swap @_ @(D '[a]) @(D '[b])

-- | A crossing drawn through an invisible node, which pins the crossing point. A plain 'swap'
-- also renders as a crossing, since 'run' fixes the order of the boundary wires and 'node' the
-- order of its ports, but Graphviz is then free to place it.
swapNode :: (Ob a, Ob b) => Dot (D [a, b]) (D [b, a])
swapNode @a @b =
  node' @[a, b] @[b, a]
    Crossing
    (Vec [":nw", ":ne"])
    (Vec [":sw", ":se"])
    "shape=point; style=invis; height=0; width=0"

node' :: (IsList as, IsList bs) => NodeKind -> Vec as String -> Vec bs String -> String -> Dot (D as) (D bs)
node' @as @bs k as bs s = Dot \n ->
  ( n + 1
  , DotData
      { inputs = fmap (\i -> Right (show n ++ (as ! i))) (ixs @as)
      , outputs = fmap (\i -> Right (show n ++ (bs ! i))) (ixs @bs)
      , edges = []
      , nodes = [(k, s)]
      }
  )

-- | A node with the given name, with a port for each input along the top and each output along
-- the bottom, in order, so that Graphviz draws the wires into it in order.
node :: forall as bs. (IsList as, IsList bs) => String -> Dot (D as) (D bs)
node s =
  node'
    Box
    (fmap (\(Fin i) -> ":i" ++ show i ++ ":n") (ixs @as))
    (fmap (\(Fin j) -> ":o" ++ show j ++ ":s") (ixs @bs))
    (portedLabel (len @as) (len @bs) s)

-- | An HTML-like label drawing the node as a rounded box: the name in the middle, with a row of
-- empty cells along the top edge for the inputs and along the bottom edge for the outputs, named
-- by the ports 'node' attaches the wires to. The wires end at the box's edge.
portedLabel :: Int -> Int -> String -> String
portedLabel ins outs s =
  "shape=plain; label=<<table border=\"1\" style=\"rounded\" cellborder=\"0\" cellspacing=\"0\" cellpadding=\"0\">"
    ++ "<tr><td>"
    ++ ports "i" ins
    ++ "</td></tr><tr><td cellpadding=\"2\">"
    ++ htmlEscape s
    ++ "</td></tr><tr><td>"
    ++ ports "o" outs
    ++ "</td></tr></table>>"
  where
    ports :: String -> Int -> String
    ports port n =
      "<table border=\"0\" cellborder=\"0\" cellspacing=\"0\" cellpadding=\"0\"><tr>"
        ++ "<td width=\"6\" height=\"6\"></td>"
        ++ List.intercalate
          "<td width=\"4\"></td>"
          ["<td port=\"" ++ port ++ show i ++ "\" width=\"10\"></td>" | i <- [0 .. n - 1 :: Int]]
        ++ "<td width=\"6\"></td></tr></table>"

-- | The nodes in the order they are reached from the inputs, going along the wires, followed by
-- any that no input reaches.
nodeOrder :: [Either x Port] -> [(Port, String, Port)] -> Int -> [Int]
nodeOrder ins es count = reached ++ [n | n <- [0 .. count - 1], n `notElem` reached]
  where
    reached = go [] [nodeOf p | Right p <- ins]
    go seen [] = reverse seen
    go seen (n : queue)
      | n `elem` seen = go seen queue
      | otherwise = go (n : seen) (queue ++ [nodeOf q | (p, _, q) <- es, nodeOf p == n])

-- | The node a port belongs to.
nodeOf :: Port -> Int
nodeOf = List.foldl' (\n c -> n * 10 + digitToInt c) 0 . takeWhile isDigit

-- | A port without its node and without the side it is drawn at (@3:o0:s@ is @:o0@); a port that
-- is only a side keeps it (@3:nw@ is @:nw@).
portOf :: Port -> String
portOf p = case break (== ':') (drop 1 (dropWhile isDigit p)) of
  (name, ':' : _) -> ':' : name
  _ -> dropWhile isDigit p

htmlEscape :: String -> String
htmlEscape = foldMap (\case '<' -> "&lt;"; '>' -> "&gt;"; '&' -> "&amp;"; c -> [c])

line :: (Ob a) => Dot (D '[a]) (D '[a])
line = id

getData :: Dot (D as) (D bs) -> DotData as bs
getData (Dot f) = snd (f 0)

run :: Dot (D as) (D bs) -> String
run d =
  let (body, _, ins, outs) = statements "" d
  in header
       ++ body
       -- the inputs at the top and the outputs at the bottom
       ++ sameRank "source" ins
       ++ sameRank "sink" outs
       ++ "\n}\n"

-- | Two parallel diagrams side by side, with an equals sign between them. Neither is simplified:
-- the picture shows two different diagrams that mean the same.
runEquation :: Dot a b -> Dot a b -> String
runEquation l@Dot{} r@Dot{} =
  let (lBody, lAnchors, lIns, lOuts) = statements "l" l
      (rBody, rAnchors, rIns, rOuts) = statements "r" r
  in header
       -- ranks shared by the two sides; a boundary rank then no longer keeps the other nodes
       -- off it, which the anchors do instead
       ++ " newrank=true;"
       ++ cluster "l" (lBody ++ lAnchors)
       ++ "\n  eq [shape=plain; label=\"=\"; fontname=\"Times\"; fontsize=24];"
       ++ cluster "r" (rBody ++ rAnchors)
       -- both inputs at the top and both outputs at the bottom, and the equals sign halfway down
       -- the left one, which keeps it on the left: tied to both, Graphviz may swap the sides
       ++ sameRank "min" (lIns ++ rIns)
       ++ sameRank "max" (lOuts ++ rOuts)
       ++ foldMap (\n -> "\n  " ++ n ++ " -> eq [style=invis];") lIns
       ++ foldMap (\n -> "\n  eq -> " ++ n ++ " [style=invis];") lOuts
       ++ "\n}\n"
  where
    cluster name body = "\n  subgraph cluster_" ++ name ++ " { peripheries=0;" ++ body ++ "\n  }"

-- | The nodes on one rank, in the given order from left to right.
sameRank :: String -> [String] -> String
sameRank _ [] = ""
sameRank rank ns =
  "\n  { rank="
    ++ rank
    ++ "; "
    ++ List.intercalate "; " ns
    ++ "; }"
    -- an edge within a rank puts its tail left of its head
    ++ foldMap (\(m, n) -> "\n  " ++ m ++ " -> " ++ n ++ " [style=invis; weight=0];") (zip ns (drop 1 ns))

-- | The start of a Graphviz graph, with the fonts and wire style of every diagram.
header :: String
header =
  "digraph G { ranksep=0.3; node [fontname=\"Times-Italic\"; shape=circle; margin=0]; edge [fontname=\"Times-Italic\"; dir=none];"

-- | The statements drawing a diagram, every node named with the prefix @p@; invisible edges
-- tying the nodes without inputs or outputs to the boundary, for when the boundary ranks do not
-- keep them inside; and the names of its input and its output boundary node. Each boundary is
-- one node with a port per wire, so that Graphviz keeps the wires in order, and is left out when
-- it has no wires.
statements :: String -> Dot (D as) (D bs) -> (String, String, [String], [String])
statements @as @bs p (Dot f) =
  let (_, DotData is os es ns) = f 0
      ins = unVec (names @as)
      outs = unVec (names @bs)
      untouched ends = [n | n <- [0 .. length ns - 1], n `notElem` ends]
      unfed = untouched ([nodeOf q | Right q <- unVec is] ++ [nodeOf q | (_, _, q) <- es])
      unused = untouched ([nodeOf q | Right q <- unVec os] ++ [nodeOf q | (q, _, _) <- es])
  in ( boundary "i" ins
         ++ boundary "o" outs
         -- node configuration, in the order the nodes are reached from the inputs: Graphviz breaks
         -- the cycles of a trace by searching in the order nodes are listed, so this makes the wires
         -- run forward from the first input
         ++ foldMap (\i -> "\n  " ++ at (show i) ++ " [" ++ snd (ns !! i) ++ "];") (nodeOrder (unVec is) es (length ns))
         -- edges from inputs
         ++ foldMap
           (\(i, n) -> "\n  " ++ at "i:p" ++ show i ++ ":s -> " ++ either (\j -> at "o:p" ++ show j ++ ":n") at n ++ ";")
           (ixed is)
         -- edges from outputs
         ++ foldMap (\(i, n) -> either (const "") (\n' -> "\n  " ++ at n' ++ " -> " ++ at "o:p" ++ show i ++ ":n;") n) (ixed os)
         -- internal edges
         ++ foldMap (\(i, s, j) -> "\n  " ++ at i ++ " -> " ++ at j ++ " [label=\"" ++ s ++ "\"];") es
     , -- a node with no wires in hangs from the inputs, and one with no wires out from the outputs
       foldMap (\n -> "\n  " ++ at "i -> " ++ at (show n) ++ " [style=invis];") [n | not (null ins), n <- unfed]
         ++ foldMap (\n -> "\n  " ++ at (show n) ++ " -> " ++ at "o [style=invis];") [n | not (null outs), n <- unused]
     , [at "i" | not (null ins)]
     , [at "o" | not (null outs)]
     )
  where
    at = (p ++)
    boundary name ws
      | null ws = ""
      | otherwise =
          "\n  "
            ++ at name
            ++ " [shape=plain; label=<<table border=\"0\" cellborder=\"0\" cellspacing=\"8\" cellpadding=\"0\"><tr>"
            ++ foldMap (\(i, n) -> "<td port=\"p" ++ show i ++ "\" width=\"24\">" ++ htmlEscape n ++ "</td>") (zip [0 :: Int ..] ws)
            ++ "</tr></table>>];"

unitAdj :: (Ob l, Ob r) => Dot (D '[]) (D '[l, r])
unitAdj = node' Box (Vec []) (Vec [":sw", ":se"]) "label=η"

counitAdj :: (Ob l, Ob r) => Dot (D '[r, l]) (D '[])
counitAdj = node' Box (Vec [":nw", ":ne"]) (Vec []) "label=ϵ"

-- | Derived operations are drawn as what they are made of.
instance Labelled DOT where
  label _ f = f

-- | The laws of @cs@, each drawn as an equation by 'runEquation', with its name. The object
-- variables are single wires @a@ to @e@, and the arrows a law asks for are 'node's with the names
-- it gives them.
lawDiagrams :: forall cs. (Laws cs, All cs DOT) => [(String, String)]
lawDiagrams = [(lawName law, draw law) | law <- laws @cs]
  where
    draw :: Law cs -> String
    draw (Law _ body) = case runIdentity (body @(D '["a"]) @(D '["b"]) @(D '["c"]) @(D '["d"]) @(D '["e"]) box) of
      l :=: r -> runEquation l r
    box :: forall (x :: DOT) y. (Ob x, Ob y) => String -> Identity (x ~> y)
    box s = Identity (node @(UN D x) @(UN D y) s)
