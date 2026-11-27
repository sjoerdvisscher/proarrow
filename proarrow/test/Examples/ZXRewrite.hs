-- | Clifford+T diagrams simplified by the hypergraph rewriting engine.
module Examples.ZXRewrite
  ( module Examples.ZXRewrite.Diagram
  , module Examples.ZXRewrite.Simplify
  , module Examples.ZXRewrite.Pictures
  , cleanupOverlapReport
  , test
  ) where

import Examples.ZXRewrite.Diagram
import Examples.ZXRewrite.Overlaps (cleanupOverlapReport)
import Examples.ZXRewrite.Pictures
import Examples.ZXRewrite.Simplify
import Examples.ZXRewrite.Tests (test)
