-- | The user-facing optics vocabulary, in one import.
--
-- * /Build/ optics with 'iso', 'lens', 'monLens', 'prism', 'affineTraversal', 'grate', 'glass',
--   'powerGrate', 'cotraversal', 'kaleidoscope', 'algebraicLens', 'classifyingLens', 'tracer',
--   'traversed', 'traversal' (from a rank-2 function on profunctors, not the van-Laarhoven form),
--   'to' and 'unto'. The results support subtyping: an optic can be used wherever a weaker flavor
--   is needed (a 'Lens' is a 'Getter', a 'Setter', a 'Fold', ...). 'MonoidalTraversal' is built
--   with 'fromPTraversal'. 'Setter', 'Fold' and 'AffineFold' have no builder; reach them by
--   'convert' from a stronger optic.
-- * /Eliminate/ optics with one eliminator per flavor: 'view' (a 'Getter'), 'review' (a 'Review'),
--   'preview' (an 'AffineFold'), 'matching' (an 'AffineTraversal'), 'over' (a 'Setter'),
--   'foldMapOf' (a 'Fold'), 'traverseOf' (a 'Traversal'), 'monTraverseOf' (a 'MonoidalTraversal'),
--   'powerGrateOf' (a 'PowerGrate'), 'cotraverseOf' (a 'Cotraversal'), 'kaleidoscopeOf' and
--   'zipWithOf' (a 'Kaleidoscope'), 'classifyOf' (an 'AlgebraicLens') and 'tracerOf' (a 'Tracer')
--   /run/ the optic, while 'withIso', 'withLens', 'withMonLens', 'withPrism', 'withGrate' and
--   'withGlass' /recover its two legs/. The operators '(^.)', '(#)', 'set', '(%~)' and '(.~)'
--   abbreviate common ones; '(^?)' and '(.?)' abbreviate 'preview' and 'classifyOf' and return a
--   plain 'Prelude.Maybe' \/ pair instead of the ambient coproduct. Writing down 'preview'\'s own
--   result type needs "Proarrow.Colimit.BinaryCoproduct" and "Proarrow.Limit.Terminal".
-- * The library's structural isos (e.g. 'Proarrow.Category.Monoidal.associator') use a second,
--   profunctor-class encoding ('Proarrow.Optic.PIso'), which every consumer above also accepts.
--   To convert between encodings, interoperate with van Laarhoven, or write flavor-generic code,
--   import "Proarrow.Optic" and its submodules.
--
-- The subtyping lattice (flavor superclass edges, weakest at the top). Dotted nodes are one-sided
-- flavors, whose methods never mention the second witness; dashed nodes are indexed by a monad and
-- so have no edge to 'Iso':
--
-- <<lattice.svg The optics subtyping lattice>>
module Proarrow.Optics
  ( -- * Optic kinds
    Optic
  , Optic'
  , Iso
  , Iso'
  , Lens
  , Lens'
  , MonoidalLens
  , MonoidalLens'
  , Prism
  , Prism'
  , AffineTraversal
  , AffineTraversal'
  , Traversal
  , Traversal'
  , MonoidalTraversal
  , MonoidalTraversal'
  , PTraversal
  , PTraversal'
  , PTraversalFull
  , Setter
  , Setter'
  , Getter
  , Review
  , AffineFold
  , Fold
  , Grate
  , Grate'
  , Glass
  , Glass'
  , PowerGrate
  , PowerGrate'
  , Cotraversal
  , Cotraversal'
  , Kaleidoscope
  , Kaleidoscope'
  , AlgebraicLens
  , ClassifyingLens
  , Tracer
  , Tracer'

    -- * Building optics
  , iso
  , lens
  , monLens
  , prism
  , affineTraversal
  , grate
  , glass
  , powerGrate
  , cotraversal
  , kaleidoscope
  , algebraicLens
  , classifyingLens
  , tracer
  , traversed
  , traversal
  , to
  , unto
  , re

    -- * Eliminating optics

    -- | Exactly one eliminator per flavor: 'view', 'review', 'preview', 'matching', 'over',
    -- 'foldMapOf', 'traverseOf', 'monTraverseOf', 'powerGrateOf', 'cotraverseOf', 'kaleidoscopeOf',
    -- 'zipWithOf', 'classifyOf' and 'tracerOf' /run/ the optic; 'withIso', 'withLens',
    -- 'withMonLens', 'withPrism', 'withGrate' and 'withGlass' /recover its two legs/.
  , view
  , review
  , preview
  , matching
  , over
  , foldMapOf
  , traverseOf
  , monTraverseOf
  , powerGrateOf
  , cotraverseOf
  , kaleidoscopeOf
  , zipWithOf
  , classifyOf
  , tracerOf
  , withIso
  , withLens
  , withMonLens
  , withPrism
  , withGrate
  , withGlass

    -- * Operators and shorthands
  , (^.)
  , (#)
  , (^?)
  , (.?)
  , set
  , (%~)
  , (.~)
  , unfold

    -- * Composing and converting optics
  , (%)
  , convert
  , Algebra (..)
  , toPTraversal
  , toPTraversalFull
  , fromPTraversal
  ) where

import Proarrow.Optic (Optic, Optic', convert, iso, re, (%))
import Proarrow.Optic.Action
  ( Algebra (..)
  , AlgebraicLens
  , ClassifyingLens
  , algebraicLens
  , classifyOf
  , classifyingLens
  , (.?)
  )
import Proarrow.Optic.AffineFold (AffineFold, preview, (^?))
import Proarrow.Optic.AffineTraversal (AffineTraversal, AffineTraversal', matching)
import Proarrow.Optic.Fold (Fold, foldMapOf, unfold)
import Proarrow.Optic.Getter (Getter, Review, review, to, unto, view, (#), (^.))
import Proarrow.Optic.Glass (Glass, Glass', glass, withGlass)
import Proarrow.Optic.Grate (Grate, Grate', grate, withGrate)
import Proarrow.Optic.Iso (Iso, Iso', withIso)
import Proarrow.Optic.Kaleidoscope
  ( Cotraversal
  , Cotraversal'
  , Kaleidoscope
  , Kaleidoscope'
  , cotraversal
  , cotraverseOf
  , kaleidoscope
  , kaleidoscopeOf
  )
import Proarrow.Optic.Lens (Lens, Lens', lens, withLens)
import Proarrow.Optic.MonoidalLens (MonoidalLens, MonoidalLens', monLens, withMonLens)
import Proarrow.Optic.MonoidalTraversal
  ( MonoidalTraversal
  , MonoidalTraversal'
  , PTraversal
  , PTraversal'
  , PTraversalFull
  , fromPTraversal
  , monTraverseOf
  , toPTraversal
  , toPTraversalFull
  , traversal
  )
import Proarrow.Optic.PowerGrate
  ( PowerGrate
  , PowerGrate'
  , powerGrate
  , powerGrateOf
  , zipWithOf
  )
import Proarrow.Optic.Prism (Prism, Prism', affineTraversal, prism, withPrism)
import Proarrow.Optic.Setter (Setter, Setter', over, set, (%~), (.~))
import Proarrow.Optic.Tracer (Tracer, Tracer', tracer, tracerOf)
import Proarrow.Optic.Traversal (Traversal, Traversal', traverseOf, traversed)
