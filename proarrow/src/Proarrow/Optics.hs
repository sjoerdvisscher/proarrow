-- | The user-facing optics vocabulary, in one import.
--
-- * /Build/ optics with 'iso', 'lens', 'monLens', 'prism', 'affineTraversal', 'grate',
--   'powerGrate', 'cotraversal', 'kaleidoscope', 'tracer', 'traversed', 'traversal' (a 'Traversal' from its van-Laarhoven \/
--   profunctor-class form), 'to' and 'unto'. These produce
--   'Proarrow.Optic.Prostrong'-flavored optics ('Iso', 'Lens', 'Prism', 'Traversal', ...), which
--   support subtyping: any optic can be used directly wherever a weaker flavor is needed (a 'Lens'
--   is a 'Getter', a 'Setter', a 'Fold', ...), checked by the 'Proarrow.Optic.SubFlavor' lattice.
--   'MonoidalTraversal' is built from its van-Laarhoven form with 'fromPTraversal'. Only the three
--   read-\/write-only flavors ('Setter', 'Fold', 'AffineFold') have no builder of their own -- reach
--   them by 'convert' from a stronger optic (or '%'-composition, as 'affineTraversal' does with a
--   'Lens' and a 'Prism').
-- * /Eliminate/ optics with exactly one canonical eliminator per flavor: 'view' (a 'Getter'),
--   'review' (a 'Review'), 'preview' (an 'AffineFold'), 'matching' (an 'AffineTraversal'), 'over'
--   (a 'Setter'), 'foldMapOf' (a
--   'Fold'), 'traverseOf' (a 'Traversal'), 'monTraverseOf' (a 'MonoidalTraversal'),
--   'powerGrateOf' (a 'PowerGrate'), 'cotraverseOf' (a 'Cotraversal'), 'kaleidoscopeOf' and 'zipWithOf' (a 'Kaleidoscope') and 'tracerOf' (a 'Tracer') /run/ the optic, while 'withIso', 'withLens',
--   'withMonLens', 'withPrism' and 'withGrate' /recover its two legs/. Operator shorthands
--   ('(^.)', '(#)', '(^?)', 'set', '(%~)', '(.~)', 'unfold') abbreviate the common ones. All of
--   these are encoding-agnostic.
-- * The library's structural isos (e.g. 'Proarrow.Category.Monoidal.associator') live in a
--   second, /profunctor-class-flavored/ encoding ('Proarrow.Optic.PIso'); every consumer above
--   accepts those as-is too, so this distinction rarely matters. When it does — converting
--   between the encodings, van Laarhoven interop, writing flavor-generic code — import
--   "Proarrow.Optic" and its submodules directly.
--
-- The full subtyping lattice ('Proarrow.Optic.SubFlavor' edges, weakest optics at the top):
--
-- >         Fold                           Setter
-- >        /    \                         /   \  \
-- >       /      \                       /     \  `----------.
-- > AffineFold    \                     /    Cotraversal     |
-- >   |    \       `---- Traversal ----'           |         |
-- >   |     \           /         \          Kaleidoscope    |
-- >   |      \         /           \               |         |
-- > Getter  AffineTraversal     MonoidalTraversal  |         |
-- >   |  \ /              \     /  /          |    |         |
-- >   |   X             .--\---'  /   Review  |  Grate     Tracer
-- >   |  / \           /    \    /    /       |    |         |
-- >  Lens   MonoidalLens    Prism----'      PowerGrate       |
-- >    \         \           /               /              /
-- >     \         \         /               /              /
-- >      `---------`---+---'---------------'--------------'
-- >                   Iso
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
  , PowerGrate
  , PowerGrate'
  , Cotraversal
  , Cotraversal'
  , Kaleidoscope
  , Kaleidoscope'
  , Tracer
  , Tracer'

    -- * Building optics
  , iso
  , lens
  , monLens
  , prism
  , affineTraversal
  , grate
  , powerGrate
  , cotraversal
  , kaleidoscope
  , tracer
  , traversed
  , traversal
  , to
  , unto
  , re

    -- * Eliminating optics

    -- | Exactly one eliminator per flavor: 'view', 'review', 'preview', 'over', 'foldMapOf',
    -- 'traverseOf', 'monTraverseOf', 'powerGrateOf', 'cotraverseOf', 'kaleidoscopeOf', 'zipWithOf' and 'tracerOf' /run/ the optic; 'withIso', 'withLens',
    -- 'withMonLens', 'withPrism' and 'withGrate' /recover its two legs/.
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
  , tracerOf
  , withIso
  , withLens
  , withMonLens
  , withPrism
  , withGrate

    -- * Operators and shorthands
  , (^.)
  , (#)
  , (^?)
  , set
  , (%~)
  , (.~)
  , unfold

    -- * Composing and converting optics
  , (%)
  , convert
  , toPTraversal
  , toPTraversalFull
  , fromPTraversal
  ) where

import Proarrow.Optic (Optic, Optic', convert, iso, re, (%))
import Proarrow.Optic.AffineFold (AffineFold, preview, (^?))
import Proarrow.Optic.AffineTraversal (AffineTraversal, AffineTraversal', matching)
import Proarrow.Optic.Fold (Fold, foldMapOf, unfold)
import Proarrow.Optic.Getter (Getter, Review, review, to, unto, view, (#), (^.))
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
