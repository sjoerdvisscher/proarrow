-- | The user-facing optics vocabulary, in one import.
--
-- * /Build/ optics with 'iso', 'lens', 'monLens', 'prism', 'grate', 'kaleidoscope', 'to' and
--   'unto'. These
--   produce 'Proarrow.Optic.Prostrong'-flavored optics ('Iso', 'Lens', 'Prism', 'Traversal', ...),
--   which support subtyping: any optic can be used directly wherever a weaker flavor is needed
--   (a 'Lens' is a 'Getter', a 'Setter', a 'Fold', ...), checked by the
--   'Proarrow.Optic.SubFlavor' lattice.
-- * /Use/ optics with 'view'\/'(^.)', 'review'\/'(#)', 'preview'\/'(^?)', 'over'\/'set'\/'(%~)'\/
--   '(.~)', 'foldMapOf', 'refold' (the mirror of 'foldMapOf' via 're'), 'traverseOf' and
--   'monTraverseOf'; /eliminate/ them to their legs with
--   'withIso', 'withLens', 'withMonLens', 'withPrism' and 'withGrate'. All of these are encoding-agnostic.
-- * The library's structural isos (e.g. 'Proarrow.Category.Monoidal.associator') live in a
--   second, /profunctor-class-flavored/ encoding ('Proarrow.Optic.PIso'); every consumer above
--   accepts those as-is too, so this distinction rarely matters. When it does — converting
--   between the encodings, van Laarhoven interop, writing flavor-generic code — import
--   "Proarrow.Optic" and its submodules directly.
--
-- The full subtyping lattice, drawn as in the @lens@\/@optics@ documentation with the weakest
-- optics at the top ('Proarrow.Optic.SubFlavor' edges point upward: each optic is usable as
-- everything above it; only covering edges are drawn):
--
-- >            Fold                             Setter
-- >           /    \                          /    |   \
-- >          /      \                        /     |  Grate
-- >    AffineFold    \                      /      |    |
-- >      |    \       `---- Traversal -----'       |    |
-- >      |     \             /       \     MonoidalLens |
-- >      |      \           /         \            |    |
-- >      |  AffineTraversal     MonoidalTraversal  |    |
-- >      |      /    \             /       \       |    |
-- >    Getter  /      \           /         \      |    |
-- >       \   /        \         /           \     |    |
-- >        Lens  Review  \      /     Kaleidoscope |    |
-- >          \     \      \    /              |    |    |
-- >           \     `---- Prism               |    |    |
-- >            \            |                 |    |    |
-- >             '-----------+-----------------+----+----'
-- >                        Iso
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
  , Setter
  , Setter'
  , Getter
  , Review
  , AffineFold
  , Fold
  , Grate
  , Grate'
  , Kaleidoscope
  , Kaleidoscope'

    -- * Building optics
  , iso
  , lens
  , monLens
  , prism
  , grate
  , kaleidoscope
  , to
  , unto
  , re

    -- * Using optics
  , view
  , viewMon
  , (^.)
  , review
  , (#)
  , preview
  , (^?)
  , over
  , set
  , (%~)
  , (.~)
  , foldMapOf
  , unfold
  , traverseOf
  , monTraverseOf
  , kaleidoscopeOf

    -- * Eliminating optics
  , withIso
  , withLens
  , withMonLens
  , withPrism
  , withGrate

    -- * Composing and converting optics
  , (%)
  , convert
  , toPTraversal
  , fromPTraversal
  , monLensToMonTraversal
  ) where

import Proarrow.Optic (Optic, Optic', convert, iso, re, (%))
import Proarrow.Optic.AffineFold (AffineFold, preview, (^?))
import Proarrow.Optic.AffineTraversal (AffineTraversal, AffineTraversal')
import Proarrow.Optic.Fold (Fold, foldMapOf, unfold)
import Proarrow.Optic.Getter (Getter, Review, review, to, unto, view, (#), (^.))
import Proarrow.Optic.Grate (Grate, Grate', grate, withGrate)
import Proarrow.Optic.Iso (Iso, Iso', withIso)
import Proarrow.Optic.Kaleidoscope (Kaleidoscope, Kaleidoscope', kaleidoscope, kaleidoscopeOf)
import Proarrow.Optic.Lens (Lens, Lens', lens, withLens)
import Proarrow.Optic.MonoidalLens (MonoidalLens, MonoidalLens', monLens, monLensToMonTraversal, viewMon, withMonLens)
import Proarrow.Optic.MonoidalTraversal
  ( MonoidalTraversal
  , MonoidalTraversal'
  , PTraversal
  , PTraversal'
  , fromPTraversal
  , monTraverseOf
  , toPTraversal
  )
import Proarrow.Optic.Prism (Prism, Prism', prism, withPrism)
import Proarrow.Optic.Setter (Setter, Setter', over, set, (%~), (.~))
import Proarrow.Optic.Traversal (Traversal, Traversal', traverseOf)
