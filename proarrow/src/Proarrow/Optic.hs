{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The encoding-agnostic core of the optics machinery: the 'Optic' type (a rank-2 profunctor
-- transformation @forall p. c p => p a b -> p s t@), optic flavors as witness-pair constraints
-- ('FLAVOR') with subtyping via 'SubFlavor', carrier strength ('Prostrong'), and the existential
-- encoding 'ExOptic' with 'ex2prof'\/'prof2ex'\/'convert' mediating between the two. Also home to
-- the flavor-generic combinators 'iso', 're' and '(%)'. The concrete optic kinds live in the
-- @Proarrow.Optic.*@ submodules, and the user-facing vocabulary (with the full subtyping lattice
-- drawn out) is re-exported from "Proarrow.Optics".
module Proarrow.Optic where

import Data.Kind (Constraint, Type)
import GHC.TypeError (ErrorMessage (..), TypeError)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..), UnOp (..))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), dimapDefault, (:~>), type (+->))
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
    :: (Ob a, Ob b, Ob s, Ob t) => {unOptic :: forall p. (c p) => p a b -> p s t} -> Optic_ (OPT a b :: OPTIC j k c) (OPT s t)

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

class (c1 p, c2 p) => (c1 :&&: c2) p
instance (c1 p, c2 p) => (c1 :&&: c2) p

infixl 9 %

-- | Compose two optics, of any (possibly different) flavors or encodings. The composite's
-- constraint is the conjunction ':&&:', which every consumer discharges one conjunct at a time
-- against its carrier -- so the composite is automatically usable at exactly the meet of the two
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

-- | Constraints @c@ that entail 'Profunctor' -- i.e. valid optic constraints. As with
-- 'SubFlavor', the quantified constraint @forall p. c p => Profunctor p@ cannot be solved
-- through superclasses (GHC #16502), so the entailment is a class method that each instance
-- discharges by ordinary superclass expansion.
class IsOptic c where
  withProfunctor :: forall p r. (c p) => ((Profunctor p) => r) -> r

instance IsOptic Profunctor where withProfunctor r = r
instance IsOptic (Prostrong w) where withProfunctor r = r
instance (IsOptic c1) => IsOptic (c1 :&&: c2) where withProfunctor @p r = withProfunctor @c1 @p r

instance
  {-# OVERLAPPABLE #-}
  (TypeError (ShowType c :<>: Text " is not an optic constraint (it does not entail Profunctor)."))
  => IsOptic c
  where
  withProfunctor _ = P.error "unreachable"

-- | Create an isomorphism from two arrows, at any optic constraint. Note that this doesn't
-- enforce that the arrows are actually inverses!
--
-- The same @iso@ builds a 'Proarrow.Optic.Iso.Iso', a 'PIso', a
-- 'Proarrow.Optic.Traversal.PTraversal', ... depending on the type it is used at; since @c@ is
-- only determined by the use site, bind the result with a type signature.
iso
  :: forall {j} {k} c (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, IsOptic c)
  => (s ~> a) -> (b ~> t) -> Optic c s t a b
iso sa bt = Optic (\ @p pab -> withProfunctor @c @p (dimap sa bt pab)) \\ sa \\ bt

type FLAVOR j k = (k +-> k) -> (j +-> j) -> Constraint

-- | The two raw facts a flavor @w@ needs so its own witnesses can be recomposed: it's closed
-- under ':.:', and it's inhabited at 'Id'. Every concrete optic kind (Lens, Prism, Setter, ...)
-- provides both as plain instances; a meta-combinator like 'Proarrow.Optic.Prod.ProdRes' needs
-- to demand them directly from its parameters wherever it has to reconstruct a witness.
type ClosedUnder :: forall {j} {k}. FLAVOR j k -> Constraint
class (forall f f' g g'. (w f f', w g g') => w (f :.: g) (g' :.: f'), w Id Id) => ClosedUnder w

instance (forall f f' g g'. (w f f', w g g') => w (f :.: g) (g' :.: f'), w Id Id) => ClosedUnder w

-- | The carrier @p@ is @w@-strong: a Tambara module for the flavor @w@. 'proact' absorbs a
-- @w@-witness pair @(f, g)@ sandwiching @p@ back into @p@, which is exactly what lets an optic
-- built from that witness distribute the carrier. The name is the profunctor (\"pro\") version of
-- "Proarrow.Category.Monoidal.Strength"'s 'Proarrow.Category.Monoidal.Strength.Strong': its
-- @proact@ specializes to @act@ at a representable carrier and to @coact@ at a corepresentable
-- one (the two are one axis, not two classes).
type Prostrong :: forall {j} {k}. FLAVOR j k -> (j +-> k) -> Constraint
class (Profunctor p, CategoryOf j, CategoryOf k) => Prostrong w (p :: j +-> k) where
  proact :: (w f g, Profunctor f, Profunctor g) => f :.: p :.: g :~> p

type ExOptic :: FLAVOR j k -> k -> j -> k -> j -> Type
data ExOptic w a b s t where
  ExIso
    :: forall {j} {k} {w :: FLAVOR j k} (s :: k) (t :: j) (a :: k) (b :: j)
     . s ~> a -> b ~> t -> ExOptic w a b s t
  ExProstrong
    :: forall {j} {k} {w :: FLAVOR j k} (p :: k +-> k) (q :: j +-> j) s t a b
     . (w p q, Profunctor p, Profunctor q)
    => (p :.: ExOptic w a b :.: q) s t -> ExOptic w a b s t

instance (CategoryOf j, CategoryOf k) => Profunctor (ExOptic w a b :: j +-> k) where
  dimap l r (ExIso f g) = ExIso (lmap l f) (rmap r g)
  dimap l r (ExProstrong @w' peq) = ExProstrong @w' (dimap l r peq)
  r \\ ExIso f g = r \\ f \\ g
  r \\ ExProstrong peq = r \\ peq

-- | The free @w@-strong profunctor is @v@-strong for every subflavor @v@ of @w@; this is what
-- lets 'convert' reinterpret optics of any encoding (composites included) at a chosen flavor.
instance (CategoryOf j, CategoryOf k, SubFlavor v w) => Prostrong v (ExOptic w a b :: j +-> k) where
  proact @f @g fpg = subFlavor @v @w @f @g (ExProstrong fpg)

ex2prof
  :: forall {j} {k} {w :: FLAVOR j k} (a :: k) (b :: j) (s :: k) (t :: j)
   . (CategoryOf j, CategoryOf k) => ExOptic w a b s t -> Optic (Prostrong w) s t a b
ex2prof (ExIso l r) = Optic (dimap l r) \\ l \\ r
ex2prof (ExProstrong (p@Objs :.: ExIso l@Objs r@Objs :.: q@Objs)) =
  Optic (\pab -> proact @w (rmap l p :.: pab :.: lmap r q))
ex2prof (ExProstrong (p :.: ex :.: q)) =
  case ex2prof ex of Optic f -> Optic (\pab -> proact @w (p :.: f pab :.: q)) \\ p \\ q

prof2ex
  :: forall {j} {k} {w :: FLAVOR j k} (a :: k) (b :: j) (s :: k) (t :: j)
   . (CategoryOf j, CategoryOf k) => Optic (Prostrong w) s t a b -> ExOptic w a b s t
prof2ex (Optic p2p) = p2p (ExIso id id)

-- | Flavor @w1@ is a subflavor of @w2@: every witness pair of @w1@ is also a witness pair of
-- @w2@, so a @'Prostrong' w1@-flavored optic is also a @'Prostrong' w2@-flavored one -- optic
-- subtyping, e.g. every lens is a getter. Optic consumers take a @SubFlavor w need@ constraint
-- (like the @Is k l@ class of the @optics@ library), so any optic of a stronger flavor can be
-- used directly where a weaker one is needed.
--
-- The instances say what the quantified constraint @forall p q. w1 p q => w2 p q@ says, but GHC
-- never expands the /given/ of a quantified constraint to its superclasses
-- (<https://gitlab.haskell.org/ghc/ghc/-/issues/16502>), which is exactly how the flavors are
-- related, so such a constraint is unsolvable for them and can't be used here. Inside an
-- instance the given is an ordinary one, so each instance of this class is just
-- @subFlavor r = r@, checked by regular superclass expansion.
--
-- The full lattice is drawn in "Proarrow.Optics".
type SubFlavor :: forall {j} {k}. FLAVOR j k -> FLAVOR j k -> Constraint
class SubFlavor w1 w2 where
  subFlavor :: forall p q r. (w1 p q) => ((w2 p q) => r) -> r

-- | Subflavoring is reflexive.
instance SubFlavor w w where subFlavor r = r

-- | Catch-all for invalid conversions, turning an unsolvable @SubFlavor@ constraint into a
-- domain-specific error message. Overlappable, so any real instance wins, and a still-abstract
-- @w@ stays deferred (the other instances are potential unifiers).
instance
  {-# OVERLAPPABLE #-}
  ( TypeError
      ( Text "A "
          :<>: ShowType w1
          :<>: Text "-flavored optic cannot be used as a "
          :<>: ShowType w2
          :<>: Text "-flavored optic."
      )
  )
  => SubFlavor w1 w2
  where
  subFlavor _ = P.error "unreachable"

-- | Convert an optic to a chosen weaker flavor, by pushing the free @w@-strong profunctor
-- @'ExOptic' w a b@ through it. This works for any input encoding: a 'Prostrong'-flavored optic
-- converts along the 'SubFlavor' lattice, a ':&&:'-composite converts when both conjuncts do,
-- and a profunctor-class-flavored optic converts when @'ExOptic' w a b@ has an instance of its
-- class (cf. 'Proarrow.Optic.Iso.fromPIso', 'Proarrow.Optic.Traversal.fromPTraversal').
--
-- Consumers accept any sufficiently strong optic directly, so this is rarely needed to /use/ an
-- optic; but constructors and '%' return their exact type monomorphically, so it is the way to
-- /store/ an optic at a weaker type, e.g. @convert ('Proarrow.Optic.Lens.lens' f g) ::
-- 'Proarrow.Optic.Traversal.Traversal'' s a@.
convert
  :: forall {j} {k} c (w :: FLAVOR j k) (s :: k) (t :: j) a b
   . (CategoryOf j, CategoryOf k, (Ob a, Ob b) => c (ExOptic w a b))
  => Optic c s t a b -> Optic (Prostrong w) s t a b
convert (Optic l) = ex2prof (l @(ExOptic w a b) (ExIso id id))

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

-- | Subflavoring is preserved by 'Flip': the mirror of every edge of the subtyping lattice also
-- holds, so e.g. @'re'@ of a lens can be used as a review ('SubFlavor' ('Flip' 'Proarrow.Optic.Lens.LensRes')
-- ('Flip' 'Proarrow.Optic.Getter.GetterRes')). Incoherent because it overlaps with the reflexive
-- instance on the diagonal, where both compute the same trivial entailment.
instance {-# INCOHERENT #-} (SubFlavor w1 w2) => SubFlavor (Flip w1) (Flip w2) where
  subFlavor @p @q r = subFlavor @w1 @w2 @q @p r

-- | 'Flip' is an involution, so @'re' . 're'@ returns to the original flavor.
instance SubFlavor w (Flip (Flip w)) where subFlavor r = r

instance SubFlavor (Flip (Flip w)) w where subFlavor r = r
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
  :: forall {k} c (s :: k) t a b
   . (forall p. (c p) => c (Op (UnOp p)))
  => Optic (OpConstraint c) s t a b -> Optic c (OP t) (OP s) (OP b) (OP a)
opOptic (Optic n) = Optic (unUnOp . n . UnOp)

unOpOptic
  :: forall {k} c (s :: k) t a b
   . Optic c (OP t) (OP s) (OP b) (OP a) -> Optic (OpConstraint c) s t a b
unOpOptic (Optic n) = Optic (unOp . n . Op)

class CompactFlavor (w :: FLAVOR j k) where
  compress
    :: (CategoryOf j, CategoryOf k)
    => ExOptic (w :: FLAVOR j k) a b s t -> (forall p q. (w p q, Profunctor p, Profunctor q) => p s a -> q b t -> r) -> r
  default compress
    :: (ClosedUnder w)
    => (CategoryOf j, CategoryOf k)
    => ExOptic w a b s t -> (forall p q. (w p q, Profunctor p, Profunctor q) => p s a -> q b t -> r) -> r
  compress (ExIso l r) k = k (Id l) (Id r)
  compress (ExProstrong (p :.: ExIso l r :.: q)) k = k (rmap l p) (lmap r q)
  compress (ExProstrong (p :.: ex :.: q)) k = compress ex \p' q' -> k (p :.: p') (q' :.: q)

withLegs
  :: (CompactFlavor (w :: FLAVOR j k), CategoryOf j, CategoryOf k)
  => (forall p q. (w p q, Profunctor p, Profunctor q) => p s a -> q b t -> r) -> Optic (Prostrong w) s t a b -> r
withLegs k (prof2ex -> ex) = compress ex k
