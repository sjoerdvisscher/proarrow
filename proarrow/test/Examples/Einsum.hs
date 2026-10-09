-- | The pictures of the wiki's einsum page: einsum specifications drawn in 'SVG', with each tensor
-- a box without inputs, and a ring of four tensors read back in three ways.
module Examples.Einsum where

import Data.List (isInfixOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding ((**))

import Proarrow.Category.Instance.OpenHypergraph
  ( OPENHG
  , SomeArrow
  , SomeSort
  , Wires
  , openHypergraph
  , readBack
  , readBackWith
  , someArrow
  )
import Proarrow.Category.Instance.OpenHypergraph qualified as OH
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..))
import Proarrow.Object (SomeOf (..))
import Proarrow.Testing (check)
import Proarrow.Tools.Diagrams.Svg (Options (..), SVG (..), Svg, W (..), defaultOptions, node, renderWith)
import Proarrow.Tools.Einsum (Tensor, einsum)

-- | The wire of an index.
type X c = S '[Wire c]

-- | Caps and cups for the spiders between two wires, and the points moved next to what they meet.
bent :: Options
bent = defaultOptions{bendSpiders = True, slidePoints = True}

draw :: Svg (S as) (S bs) -> String
draw = renderWith bent

a2, b2 :: Tensor '[X "i", X "j"]
a2 = Str (node @'[I] @'[Wire "i", Wire "j"] "A")
b2 = Str (node @'[I] @'[Wire "i", Wire "j"] "B")

a1, b1 :: Tensor '[X "i"]
a1 = Str (node @'[I] @'[Wire "i"] "a")
b1 = Str (node @'[I] @'[Wire "i"] "b")

aii :: Tensor '[X "i", X "i"]
aii = Str (node @'[I] @'[Wire "i", Wire "i"] "A")

bjk :: Tensor '[X "j", X "k"]
bjk = Str (node @'[I] @'[Wire "j", Wire "k"] "B")

-- | The standard examples, each with the file the wiki shows it in.
gallery :: [(FilePath, String)]
gallery =
  [ ("matmul.svg", draw (unStr (einsum @"ij,jk->ik" a2 bjk)))
  , ("transpose.svg", draw (unStr (einsum @"ij->ji" a2)))
  , ("trace.svg", draw (unStr (einsum @"ii->" aii)))
  , ("diagonal.svg", draw (unStr (einsum @"ii->i" aii)))
  , ("sum.svg", draw (unStr (einsum @"ij->" a2)))
  , ("row-sums.svg", draw (unStr (einsum @"ij->i" a2)))
  , ("dot.svg", draw (unStr (einsum @"i,i->" a1 b1)))
  , ("outer.svg", draw (unStr (einsum @"i,j->ij" a1 (Str (node @'[I] @'[Wire "j"] "b") :: Tensor '[X "j"]))))
  , ("entrywise.svg", draw (unStr (einsum @"ij,ij->ij" a2 b2)))
  , ("copy.svg", draw (unStr (einsum @"i->ii" a1)))
  ]

-- * The ring

t :: Tensor '[X "i", X "j", X "x"]
t = Str (node @'[I] @'[Wire "i", Wire "j", Wire "x"] "T")

u :: Tensor '[X "j", X "k", X "k"]
u = Str (node @'[I] @'[Wire "j", Wire "k", Wire "k"] "U")

v :: Tensor '[X "k", X "l"]
v = Str (node @'[I] @'[Wire "k", Wire "l"] "V")

w :: Tensor '[X "l", X "i"]
w = Str (node @'[I] @'[Wire "l", Wire "i"] "W")

-- | The ring as einsum draws it in 'SVG', where every wire has the same size.
ringEinsum :: String
ringEinsum = draw (unStr (einsum @"kl,jkk,ijx,li->li" v u t w))

-- | The nodes of the ring, numbered from 0: i, j, x, k and l.
ringSorts :: [SomeSort SVG]
ringSorts = [Some @(X "i"), Some @(X "j"), Some @(X "x"), Some @(X "k"), Some @(X "l")]

-- | The open hypergraph of the ring with the given boxes, and its boundary the nodes l and i.
ring :: [OH.Box String Int] -> Wires '[] ~> (Wires '[X "l", X "i"] :: OPENHG SVG String)
ring bxs = either error id (openHypergraph ringSorts [] [4, 0] bxs)

-- | The ring with the dimensions of the matrices on the wiki page: i and k have 2, j, x and l have 3.
matSize :: SomeSort SVG -> Int
matSize s = if any (OH.sameSort s) ([Some @(X "j"), Some @(X "x"), Some @(X "l")] :: [SomeSort SVG]) then 3 else 2

ringArrow :: String -> SomeArrow SVG
ringArrow x = case x of
  "T" -> someArrow t
  "U" -> someArrow u
  "V" -> someArrow v
  "W" -> someArrow w
  _ -> someArrow (v ** u ** t ** w)

drawRead :: Either String (Strictified '[] '[X "l", X "i"]) -> String
drawRead = either error (draw . unStr)

-- | The ring as einsum reads it back with the sizes of the matrices.
ringSized :: String
ringSized =
  drawRead
    ( readBackWith
        matSize
        ringArrow
        (ring [OH.Box "V" [] [3, 4], OH.Box "U" [] [1, 3, 3], OH.Box "T" [] [0, 1, 2], OH.Box "W" [] [4, 0]])
    )

-- | The ring with everything tensored first: one box that is all four tensors side by side, whose
-- ports are joined afterwards.
ringNaive :: String
ringNaive = drawRead (readBack ringArrow (ring [OH.Box "VUTW" [] [3, 4, 1, 3, 3, 0, 1, 2, 4, 0]]))

-- | The ring pictures, each with the file the wiki shows it in.
ringPictures :: [(FilePath, String)]
ringPictures = [("ring-naive.svg", ringNaive), ("ring-einsum.svg", ringEinsum), ("ring-sized.svg", ringSized)]

test :: TestTree
test =
  testGroup
    "Einsum pictures"
    [ testProperty ("draws " ++ file) (check "not an SVG document" ("<svg" `isInfixOf` svg))
    | (file, svg) <- gallery ++ ringPictures
    ]
