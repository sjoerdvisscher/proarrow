-- | The user-facing optics vocabulary, in one import.
--
-- * /Build/ optics with 'iso', 'lens', 'monLens', 'prism', 'affineTraversal', 'grate', 'glass',
--   'powerGrate', 'cotraversal', 'kaleidoscope', 'algebraicLens', 'classifyingLens', 'tracer',
--   'traversed', 'traversal' (a 'Traversal' from its profunctor-class form -- a rank-2 function
--   on profunctors, not the van-Laarhoven encoding), 'to' and 'unto'. These produce
--   'Proarrow.Optic.Prostrong'-flavored optics ('Iso', 'Lens', 'Prism', 'Traversal', ...), which
--   support subtyping: any optic can be used directly wherever a weaker flavor is needed (a 'Lens'
--   is a 'Getter', a 'Setter', a 'Fold', ...), checked by the flavor superclass lattice.
--   'MonoidalTraversal' is built with 'fromPTraversal', from the profunctor-class form 'PTraversal'
--   (see /Beyond this import/ below). Only the three
--   read-\/write-only flavors ('Setter', 'Fold', 'AffineFold') have no builder of their own -- reach
--   them by 'convert' from a stronger optic (or '%'-composition, as 'affineTraversal' does with a
--   'Lens' and a 'Prism').
-- * /Eliminate/ optics with exactly one canonical eliminator per flavor: 'view' (a 'Getter'),
--   'review' (a 'Review'), 'preview' (an 'AffineFold'), 'matching' (an 'AffineTraversal'), 'over'
--   (a 'Setter'), 'foldMapOf' (a
--   'Fold'), 'traverseOf' (a 'Traversal'), 'monTraverseOf' (a 'MonoidalTraversal'),
--   'powerGrateOf' (a 'PowerGrate'), 'cotraverseOf' (a 'Cotraversal'), 'kaleidoscopeOf' and
--   'zipWithOf' (a 'Kaleidoscope'), 'classifyOf' (an 'AlgebraicLens') and 'tracerOf' (a 'Tracer')
--   /run/ the optic, while 'withIso', 'withLens',
--   'withMonLens', 'withPrism', 'withGrate' and 'withGlass' /recover its two legs/. Operator
--   shorthands ('(^.)', '(#)', 'set', '(%~)', '(.~)') abbreviate the common ones, and '(^?)' and
--   '(.?)' abbreviate 'preview' and 'classifyOf' while also landing the result in a plain
--   'Prelude.Maybe' \/ pair rather than the ambient category's coproduct. All of these are
--   encoding-agnostic. Note that 'preview'\'s own result type is stated with @||@ and
--   @TerminalObject@, so writing that type down needs "Proarrow.Colimit.BinaryCoproduct" and
--   "Proarrow.Limit.Terminal".
-- * The library's structural isos (e.g. 'Proarrow.Category.Monoidal.associator') live in a
--   second, /profunctor-class-flavored/ encoding ('Proarrow.Optic.PIso'); every consumer above
--   accepts those as-is too, so this distinction rarely matters. When it does — converting
--   between the encodings, van Laarhoven interop, writing flavor-generic code — import
--   "Proarrow.Optic" and its submodules directly.
--
-- The full subtyping lattice (flavor superclass edges, weakest optics at the top).
-- Dotted nodes are one-sided flavors, whose methods never mention the second witness; dashed
-- nodes are indexed by a monad and so have no edge to 'Iso':
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
