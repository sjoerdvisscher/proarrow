-- | Composition in the Int construction, drawn. Over "Proarrow.Tools.Diagrams.Svg", which is traced,
-- two Int morphisms with boxes @g@ and @f@ compose to a diagram whose traced wires are the middle
-- object's two halves. The composition is the @rec@ block in
-- "Proarrow.Category.Instance.IntConstruction".
module Examples.IntComposition (test, compositionPicture) where

import Data.List (isInfixOf)
import Test.Tasty (TestTree)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Instance.IntConstruction (INT (..), IntConstruction (..))
import Proarrow.Core (Promonad (..))
import Proarrow.Testing (check)
import Proarrow.Tools.Diagrams.Svg (SVG (..), W (Wire), node, render)

type W1 s = S '[Wire s]

gInt :: IntConstruction (I (W1 "a⁺") (W1 "a⁻")) (I (W1 "b⁺") (W1 "b⁻"))
gInt = Int (node @'[Wire "a⁺", Wire "b⁻"] @'[Wire "a⁻", Wire "b⁺"] "g")

fInt :: IntConstruction (I (W1 "b⁺") (W1 "b⁻")) (I (W1 "c⁺") (W1 "c⁻"))
fInt = Int (node @'[Wire "b⁺", Wire "c⁻"] @'[Wire "b⁻", Wire "c⁺"] "f")

-- | @f . g@ in the Int construction, as the underlying traced diagram.
compositionPicture :: String
compositionPicture = case fInt . gInt of Int h -> render h

test :: TestTree
test =
  testProperty "Int composition draws" $
    check "not an SVG document" ("<svg" `isInfixOf` compositionPicture)
