-- | The user-facing optics vocabulary, in one import.
--
-- * /Build/ optics with 'iso', 'lens', 'prism', 'grate', 'kaleidoscope', 'to' and
--   'unto'. These
--   produce 'Proarrow.Optic.Prostrong'-flavored optics ('Iso', 'Lens', 'Prism', 'Traversal', ...),
--   which support subtyping: any optic can be used directly wherever a weaker flavor is needed
--   (a 'Lens' is a 'Getter', a 'Setter', a 'Fold', ...), checked by the
--   'Proarrow.Optic.SubFlavor' lattice.
-- * /Use/ optics with 'view'\/'(^.)', 'review'\/'(#)', 'preview'\/'(^?)', 'over'\/'set'\/'(%~)'\/
--   '(.~)', 'foldMapOf', 'refold' (the mirror of 'foldMapOf' via 're') and 'traverseOf'; /eliminate/ them to their legs with
--   'withIso', 'withLens', 'withPrism' and 'withGrate'. All of these are encoding-agnostic.
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
-- >           Fold                     Setter
-- >          /    \                   /    \
-- >         /      \                 /      \
-- >   AffineFold    \               /       Grate
-- >     |    \       \             /           |
-- >     |     \       `-Traversal-'            |
-- >     |      \           |                   |
-- >     |   AffineTraversal-'                  |
-- >     |       /  \                           |
-- >   Getter   /    \    Review                |
-- >       \   /      \    /                    |
-- >        Lens       Prism                    |
-- >          \          \                      |
-- >           '----------'--,-----------------'
-- >                        Iso
--
-- A mirror symmetry sits around 'Iso' at the base: 'Lens'\/'Getter' reflect into
-- 'Prism'\/'Review' (product residual vs. coproduct residual, viewing vs. reviewing), meeting
-- at 'AffineTraversal'. Above, 'Traversal' reaches both 'Fold' and 'Setter', flanked by
-- 'AffineFold' (folds but never sets) and 'Grate' (sets but never folds, its residual living
-- under an exponential rather than a tensor). @Review@'s own mirror image of the fold chain, and
-- the reverse of any optic, exist generically via 'Proarrow.Optic.Flip'\/'Proarrow.Optic.re' and
-- are omitted here.
--
-- There is deliberately no separate co-traversal optic: for the /representable/ witnesses one can
-- actually construct, a \"cotraversal\" coincides with a 'Lens'\/'Traversal' (a comonoid-tensor
-- residual is just a lens residual), so it adds nothing to the lattice; genuine reversals are
-- 'Proarrow.Optic.re'.
--
-- Not drawn (it would clutter the 'Traversal' branch): a refinement /below/
-- 'Traversal', 'Proarrow.Optic.Kaleidoscope.Kaleidoscope'. Its witness presents @s@ as a fixed
-- tensor /power/ of the focus (@s ~> a ** ... ** a@), a genuine decomposition, so it is really a
-- fixed-arity traversal -- it folds and sets like any traversal. What makes it /more/ than a
-- traversal is that its 'Proarrow.Optic.Kaleidoscope.kaleidoP' distributes an arbitrary
-- 'Proarrow.Category.Monoidal.MonoidalProfunctor' (the @Applicative@\/zip structure), including
-- the non-'Proarrow.Category.Monoidal.Distributive.StrongDistributiveProfunctor' carriers (e.g.
-- @Costar f@) an ordinary traversal cannot distribute -- letting it /aggregate/ foci with @**@,
-- not only replace them. (Note this is a property of the /representable/ witnesses built here; a
-- genuinely non-decomposing, build-only kaleidoscope would need a non-representable
-- free-@Applicative@ witness, which is not provided.)
--
-- Its placement is bounded on both sides: 'Proarrow.Optic.Kaleidoscope.Kaleidoscope' is usable
-- as a 'Traversal' (hence 'Fold'\/'Setter'), and only an 'Iso' is usable as a kaleidoscope --
-- @Lens@\/@Prism@\/@Grate@ are not, since their residuals need strength that a bare
-- 'Proarrow.Category.Monoidal.MonoidalProfunctor' carrier lacks, whereas an iso is just the
-- trivial arity-one kaleidoscope.
module Proarrow.Optics
  ( -- * Optic kinds
    Optic
  , Optic'
  , Iso
  , Iso'
  , Lens
  , Lens'
  , Prism
  , Prism'
  , AffineTraversal
  , Traversal
  , Traversal'
  , Setter
  , Setter'
  , Getter
  , Review
  , AffineFold
  , Fold
  , Grate
  , Kaleidoscope

    -- * Building optics
  , iso
  , lens
  , prism
  , grate
  , kaleidoscope
  , to
  , unto
  , re

    -- * Using optics
  , view
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
  , kaleidoscopeOf

    -- * Eliminating optics
  , withIso
  , withLens
  , withPrism
  , withGrate

    -- * Composing and converting optics
  , (%)
  , convert
  ) where

import Proarrow.Optic (Optic, Optic', convert, iso, re, (%))
import Proarrow.Optic.AffineFold (AffineFold, preview, (^?))
import Proarrow.Optic.AffineTraversal (AffineTraversal)
import Proarrow.Optic.Fold (Fold, foldMapOf, unfold)
import Proarrow.Optic.Getter (Getter, Review, review, to, unto, view, (#), (^.))
import Proarrow.Optic.Grate (Grate, grate, withGrate)
import Proarrow.Optic.Iso (Iso, Iso', withIso)
import Proarrow.Optic.Kaleidoscope (Kaleidoscope, kaleidoscope, kaleidoscopeOf)
import Proarrow.Optic.Lens (Lens, Lens', lens, withLens)
import Proarrow.Optic.Prism (Prism, Prism', prism, withPrism)
import Proarrow.Optic.Setter (Setter, Setter', over, set, (%~), (.~))
import Proarrow.Optic.Traversal (Traversal, Traversal', traverseOf)
