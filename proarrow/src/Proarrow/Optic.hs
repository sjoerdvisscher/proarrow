{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The encoding-agnostic core of the optics machinery: the 'Optic' type (a rank-2 profunctor
-- transformation @forall p. c p => p a b -> p s t@), optic flavors as witness-pair constraints
-- ('FLAVOR') with subtyping via flavor superclasses, carrier strength ('Prostrong'), and the existential
-- encoding 'ExOptic' with 'ex2prof'\/'prof2ex'\/'convert' mediating between the two. Also home to
-- the flavor-generic combinators 'iso', 're' and '(%)'. The concrete optic kinds live in the
-- @Proarrow.Optic.*@ submodules, and the user-facing vocabulary (with the full subtyping lattice
-- drawn out) is re-exported from "Proarrow.Optics".
module Proarrow.Optic where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..), UnOp (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , dimapDefault
  , (:~>)
  , type (+->)
  , type (:&&:)
  )
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

type data OPTIC (j :: Kind) (k :: Kind) (c :: j +-> k -> Constraint) = OPT k j
type family OptL (p :: OPTIC j k c) where
  OptL (OPT j k) = j
type family OptR (p :: OPTIC j k c) where
  OptR (OPT j k) = k
type Optic_ :: CAT (OPTIC j k c)
data Optic_ ab st where
  Optic
    :: (Ob a, Ob b, Ob s, Ob t)
    => {unOptic :: forall p. (c p, Profunctor p) => p a b -> p s t} -> Optic_ (OPT a b :: OPTIC j k c) (OPT s t)

instance (CategoryOf j, CategoryOf k) => Profunctor (Optic_ :: CAT (OPTIC j k c)) where
  dimap = dimapDefault
  r \\ Optic{} = r
instance (CategoryOf j, CategoryOf k) => Promonad (Optic_ :: CAT (OPTIC j k c)) where
  id = Optic id
  Optic n . Optic m = Optic (n . m)

-- | Optics form a category: an object @'OPT' s t@ pairs the object @s@ an optic reads from
-- (contravariant) with the object @t@ it writes back (covariant), an arrow
-- @'OPT' a b '~>' 'OPT' s t@ is a @c@-flavored optic with focus @a@\/@b@ inside @s@\/@t@, and
-- composition is optic composition.
instance (CategoryOf j, CategoryOf k) => CategoryOf (OPTIC j k c) where
  type (~>) = Optic_
  type Ob opt = (opt ~ OPT (OptL opt) (OptR opt), Ob (OptL opt), Ob (OptR opt))

type Optic (c :: j +-> k -> Constraint) s t a b = Optic_ (OPT a b) (OPT s t :: OPTIC j k c)
type Optic' c s a = Optic c s s a a

infixl 9 %

-- | Compose two optics, of any (possibly different) flavors or encodings. The composite's constraint
-- is the conjunction ':&&:', so the composite is automatically usable at exactly the meet of the two
-- flavors' capabilities: a lens composed with a prism previews, folds, traverses and sets, but
-- no longer views or reviews. Use 'convert' to name the composite at a single flavor for
-- storage, e.g. @'convert' (l % p) :: 'Proarrow.Optic.AffineTraversal.AffineTraversal' s t a b@.
(%) :: Optic c1 s t a b -> Optic c2 a b c d -> Optic (c1 :&&: c2) s t c d
Optic n % Optic m = Optic (n . m)

-- | An iso in the profunctor-class-flavored encoding (the @P@-prefix convention: plain optic
-- names belong to the 'Prostrong'-flavored encoding, @P@-prefixed ones to the
-- profunctor-class-flavored one). Convert with 'Proarrow.Optic.Iso.fromPIso' and
-- 'Proarrow.Optic.Iso.toPIso'.
type PIso s t a b = Optic Profunctor s t a b

type PIso' s a = PIso s s a a

-- | Create an isomorphism from two arrows, at any optic constraint. Note that this doesn't
-- enforce that the arrows are actually inverses!
--
-- The same @iso@ builds a 'Proarrow.Optic.Iso.Iso', a 'PIso', a
-- 'Proarrow.Optic.Traversal.PTraversal', ... depending on the type it is used at; since @c@ is
-- only determined by the use site, bind the result with a type signature.
iso
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k)
  => (s ~> a) -> (b ~> t) -> Optic c s t a b
iso sa bt = Optic (dimap sa bt) \\ sa \\ bt

type FLAVOR j k = (k +-> k) -> (j +-> j) -> Constraint

-- | A flavor: a class of witness pairs that is closed under composition and contains the identity
-- pair -- the monoidal structure of the residuals, with @(Id, Id)@ as unit and
-- @(f :.: g, g' :.: f')@ (note the reversal on the right) as tensor.
type Flavor :: forall {j} {k}. FLAVOR j k -> Constraint
class (forall f f' g g'. (w f f', w g g') => w (f :.: g) (g' :.: f'), w Id Id) => Flavor w where
  composeFlavor :: forall f f' g g' r. (w f f', w g g') => ((w (f :.: g) (g' :.: f')) => r) -> r

instance (forall f f' g g'. (w f f', w g g') => w (f :.: g) (g' :.: f'), w Id Id) => Flavor w where
  composeFlavor r = r

-- | @w p q@, as a class with a single instance instead of a bare constraint. The subtyping
-- quantified constraint is spelled @forall p q. v p q => Sub w p q@ rather than
-- @forall p q. v p q => w p q@ because GHC refuses to solve the head of a quantified constraint
-- from a superclass of its premise unless that superclass is strictly smaller than the head (its
-- safeguard against superclass loops in instance declarations), and @w p q@ is never smaller
-- than itself; behind the 'Sub' instance @w p q@ is an ordinary wanted, solved from the
-- superclasses of @v p q@ as usual. 'sub' hands @w p q@ back as an ordinary given (see 'Flavor').
--
-- Deliberately without @w p q@ as a superclass: with it, a quantified given @forall p q. w p q =>
-- Sub IsoFl p q@ would reach @'Profunctor' p@ through the flavor superclasses, which makes GHC
-- treat it as a potential match for every @Profunctor@ wanted in scope and reject the ordinary
-- instances as overlapping.
type Sub :: forall {j} {k}. FLAVOR j k -> FLAVOR j k
class Sub w p q where
  sub :: ((w p q) => r) -> r

instance (w p q) => Sub w p q where
  sub r = r

-- | The carrier @p@ is @w@-strong: a Tambara module for the flavor @w@. 'proact' absorbs a
-- @w@-witness pair @(f, g)@ sandwiching @p@ back into @p@, which is exactly what lets an optic
-- built from that witness distribute the carrier. The name is the profunctor (\"pro\") version of
-- "Proarrow.Category.Monoidal.Strength"'s 'Proarrow.Category.Monoidal.Strength.Strong': its
-- @proact@ specializes to @act@ for certain 'Rep'/'Corep' pairs and to @coact@ for
-- certain 'Corep'/'Rep' ones.
type Prostrong :: forall {j} {k}. FLAVOR j k -> (j +-> k) -> Constraint
class (Profunctor p, CategoryOf j, CategoryOf k) => Prostrong w (p :: j +-> k) where
  proact :: (w f g, Profunctor f, Profunctor g) => f :.: p :.: g :~> p

-- | The existential encoding of an optic.
type ExOptic :: forall {j} {k}. FLAVOR j k -> k -> j -> j +-> k
data ExOptic w a b s t where
  ExOptic
    :: forall {j} {k} {w :: FLAVOR j k} (p :: k +-> k) (q :: j +-> j) (s :: k) (t :: j) a b
     . (w p q, Profunctor p, Profunctor q) => p s a -> q b t -> ExOptic w a b s t

instance (CategoryOf j, CategoryOf k) => Profunctor (ExOptic w a b :: j +-> k) where
  dimap l r (ExOptic p q) = ExOptic (lmap l p) (rmap r q)
  r \\ ExOptic p q = r \\ p \\ q

-- | The free @w@-strong profunctor is @v@-strong for every subflavor @v@ of @w@; this is what
-- lets 'convert' and 'withLegs' accept optics of any encoding (composites included). It is the one
-- bridge instance that replaces a per-carrier one for each flavor.
instance (CategoryOf j, CategoryOf k, forall p q. (v p q) => Sub w p q, Flavor w) => Prostrong v (ExOptic w a b :: j +-> k) where
  proact @f @g (f :.: ExOptic @p @q p q :.: g) = sub @w @f @g (composeFlavor @w @f @g @p @q (ExOptic (f :.: p) (q :.: g)))

-- | Build a 'Prostrong'-flavored optic from a @w@-witness pair (the two legs @p s a@ and @q b t@)
-- by wrapping them around the carrier with one 'proact'. Every optic constructor
-- ('Proarrow.Optic.Lens.lens', 'Proarrow.Optic.Prism.prism', ...) is @legs2prof@ of its generating
-- witness pair; 'ex2prof' is the same on the packaged 'ExOptic'.
legs2prof
  :: forall {j} {k} (w :: FLAVOR j k) p q (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, w p q, Profunctor p, Profunctor q)
  => p s a -> q b t -> Optic (Prostrong w) s t a b
legs2prof p q = Optic (\pab -> proact @w (p :.: pab :.: q)) \\ p \\ q

ex2prof
  :: forall {j} {k} {w :: FLAVOR j k} (a :: k) (b :: j) (s :: k) (t :: j)
   . (CategoryOf j, CategoryOf k) => ExOptic w a b s t -> Optic (Prostrong w) s t a b
ex2prof (ExOptic p q) = legs2prof @w p q

-- | Run an optic, in any encoding, at its own witness pair (the Pastro-Street move): a
-- 'Prostrong'-flavored optic discharges @c ('ExOptic' w a b)@ through the bridge instance above
-- (i.e. @forall p q. v p q => 'Sub' w p q@), a '(%)'-composite one conjunct at a time, and a profunctor-class-flavored
-- one through the carrier's own instances of its class.
prof2ex
  :: forall {j} {k} w c (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, Flavor w, (Ob a, Ob b) => c (ExOptic w a b))
  => Optic c s t a b -> ExOptic w a b s t
prof2ex (Optic l) = l @(ExOptic w a b) (ExOptic (Id id) (Id id))

-- | 'prof2ex' in continuation-passing form: the generic eliminator.
withLegs
  :: forall {j} {k} w c (s :: k) (t :: j) a b r
   . (CategoryOf j, CategoryOf k, Flavor w, (Ob a, Ob b) => c (ExOptic w a b))
  => Optic c s t a b -> (forall p q. (w p q, Profunctor p, Profunctor q) => p s a -> q b t -> r) -> r
withLegs o k = case prof2ex @w o of ExOptic p q -> k p q

-- | Convert an optic to a chosen flavor @w@, by running it at its existential encoding
-- @'ExOptic' w a b@ and wrapping the resulting witness pair back around the carrier: this works for
-- any input encoding. A 'Prostrong'-flavored optic converts along the subtyping lattice (via the
-- bridge instance of 'ExOptic'; an invalid conversion fails with @Could not deduce (w p q)@ for the
-- missing superclass), a ':&&:'-composite converts when both conjuncts do, and a
-- profunctor-class-flavored optic converts when @'ExOptic' w a b@ has an instance of its class -- which
-- it does for every class whose generating witnesses @w@ contains (cf. 'Proarrow.Optic.Iso.fromPIso',
-- 'Proarrow.Optic.MonoidalTraversal.fromPTraversal', 'Proarrow.Optic.Tracer.fromPTracer').
--
-- Consumers accept any sufficiently strong optic directly, so this is rarely needed to /use/ an
-- optic; but constructors and '%' return their exact type monomorphically, so it is the way to
-- /store/ an optic at a weaker type, e.g. @convert ('Proarrow.Optic.Lens.lens' f g) ::
-- 'Proarrow.Optic.Traversal.Traversal'' s a@.
convert
  :: forall {j} {k} c (w :: FLAVOR j k) (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, Flavor w, (Ob a, Ob b) => c (ExOptic w a b))
  => Optic c s t a b -> Optic (Prostrong w) s t a b
convert o = withLegs @w o (legs2prof @w)

-- | The reversing carrier implementing 're': it stores a continuation @p b a -> p t s@, so
-- running an optic at @'Re' p _ _@ builds the optic turned around. Its 'Prostrong' instance
-- absorbs the witness pair mirrored, via 'Flip'.
data Re p s t a b where
  Re :: (Ob a, Ob b) => {unRe :: p b a -> p t s} -> Re p s t a b

instance (Profunctor p) => Profunctor (Re p s t) where
  dimap l r (Re f) = Re (f . dimap r l) \\ l \\ r
  r \\ Re{} = r

class
  (forall p a b. (coc p) => c (Re p a b)) =>
  ReversibleOptic (c :: j +-> k -> Constraint) (coc :: k +-> j -> Constraint)
    | c -> coc

instance ReversibleOptic Profunctor Profunctor
instance (ReversibleOptic l l', ReversibleOptic r r') => ReversibleOptic (l :&&: r) (l' :&&: r')
instance ReversibleOptic (Prostrong w) (Prostrong (Flip w))

re :: (Ob a, Ob b, ReversibleOptic c coc) => Optic c s t a b -> Optic coc b a t s
re (Optic l) = Optic (unRe (l (Re id)))

class (w p q) => Flip w q p
instance (w p q) => Flip w q p

instance (CategoryOf j, CategoryOf k, Prostrong (Flip w) p) => Prostrong w (Re p s t :: k +-> j) where
  proact (f@Objs :.: Re n :.: g@Objs) = Re \p -> n (proact @(Flip w) @p (g :.: p :.: f))

class (c (Op q)) => OpConstraint c q
instance (c (Op q)) => OpConstraint c q

class (w (Op g) (Op f)) => OpFlavor w f g
instance (w (Op g) (Op f)) => OpFlavor w f g

instance (Prostrong w p, CategoryOf j, CategoryOf k) => Prostrong (OpFlavor w) (UnOp p :: j +-> k) where
  proact (f :.: UnOp p :.: g) = UnOp (proact @w (Op g :.: p :.: Op f))

instance (Prostrong w p, CategoryOf j, CategoryOf k) => Prostrong w (Op (UnOp p :: j +-> k)) where
  proact (f@Objs :.: Op (UnOp p) :.: g@Objs) = Op (UnOp (proact @w (f :.: p :.: g)))

opOptic
  :: forall {j} {k} c (s :: j) (t :: k) a b
   . (forall p. (c p) => c (Op (UnOp p)), CategoryOf j, CategoryOf k)
  => Optic (OpConstraint c) s t a b -> Optic c (OP t) (OP s) (OP b) (OP a)
opOptic (Optic n) = Optic (unUnOp . n . UnOp)

unOpOptic
  :: forall {k} c (s :: k) t a b
   . Optic c (OP t) (OP s) (OP b) (OP a) -> Optic (OpConstraint c) s t a b
unOpOptic (Optic n) = Optic (unOp . n . Op)
