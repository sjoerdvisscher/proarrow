{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A profunctor-specific counterpart of "Proarrow.Bicategory.Strictified", hardcoded to
-- @:.:@\/'Id' instead of an arbitrary 'Proarrow.Bicategory.Bicategory'. A 'Path' is a
-- type-level list of profunctors; 'Fold' collapses one down to the single profunctor its
-- elements compose to. Unlike the general (strictified) version, we don't need to track
-- identity 2-cells through the induction -- since our 2-cells are just plain Haskell
-- functions (@:~>@), the identity of any composite is always definitionally @\\x -> x@.
-- The only real work is 'concatFold'\/'splitFold', which do the actual
-- associator\/unitor reshuffling once, by induction, so that "Proarrow.Squares" never has
-- to.
module Proarrow.Path where

import Data.Kind (Constraint, Type)
import Prelude (type (~))

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, src, tgt, (:~>), type (+->))
import Proarrow.Profunctor.Instance.Composition (o, (:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Representable)

infixr 5 :::
infixl 5 +++

-- | Identity natural transformation, used as a 2-cell between profunctors that happen to
-- be syntactically equal.
idN :: p :~> p
idN x = x

-- @:.:@\/'Id' aren't strictly associative\/unital, unlike the 'Proarrow.Bicategory.O'\/
-- 'Proarrow.Bicategory.I' of a strictified bicategory.
leftUnitor :: (Profunctor p) => Id :.: p :~> p
leftUnitor (Id l :.: p) = lmap l p

leftUnitorInv :: (Profunctor p) => p :~> Id :.: p
leftUnitorInv p = Id (src p) :.: p

rightUnitor :: (Profunctor p) => p :.: Id :~> p
rightUnitor (p :.: Id r) = rmap r p

rightUnitorInv :: (Profunctor p) => p :~> p :.: Id
rightUnitorInv p = p :.: Id (tgt p)

associator :: (p :.: q) :.: r :~> p :.: (q :.: r)
associator ((p :.: q) :.: r) = p :.: (q :.: r)

associatorInv :: p :.: (q :.: r) :~> (p :.: q) :.: r
associatorInv (p :.: (q :.: r)) = (p :.: q) :.: r

-- | A type-level list of profunctors, from category @j@ to category @k@.
type Path :: Type -> Type -> Type
type data Path j k where
  Nil :: Path k k
  (:::) :: (i +-> j) -> Path j k -> Path i k

type family (+++) (ps :: Path a b) (qs :: Path b c) :: Path a c
type instance Nil +++ qs = qs
type instance (p ::: ps) +++ qs = p ::: (ps +++ qs)

-- | @(as +++ bs) +++ cs@ and @as +++ (bs +++ cs)@ are the same 'Path'. Proved once, up
-- front, by (mutual) induction with 'IsOb'\'s superclasses -- see there for how the
-- induction actually goes through -- so that every other associativity fact needed
-- anywhere in "Proarrow.Squares" is a free @~@ coercion instead of a function call.
class ((as +++ bs) +++ cs ~ as +++ (bs +++ cs)) => Assoc as bs cs

instance (as +++ (bs +++ cs) ~ (as +++ bs) +++ cs) => Assoc as bs cs

-- | Fold a 'Path' down to the single profunctor its elements compose to.
type family Fold (ps :: Path j k) :: j +-> k

type instance Fold (Nil :: Path j j) = Id
type instance Fold (p ::: Nil) = p
type instance Fold (p ::: (q ::: ps)) = Fold (q ::: ps) :.: p

-- | Which per-element property a 'SPath' witnesses. @Tight@ plays the role of the tight
-- (vertical, 'Representable') legs of the @Prof@ equipment; a later @Cotight@ would do
-- the same for 'Proarrow.Profunctor.Corepresentable.Corepresentable' legs.
data Tag = Prof | Tight

-- | The per-element constraint a 'Tag' stands for. @c@ is applied homogeneously at every
-- element of a path, each of a (potentially) different @i +-> j@ kind -- a genuinely
-- impredicative use GHC's kind system can't express with @c@ itself as the parameter, so
-- 'Tag' is the (monomorphic, first-order) proxy for it instead. Mirrors
-- "Proarrow.Bicategory.Sub"'s @IsOb@\/@SUBCAT@ tag mechanism.
type family Sat (t :: Tag) (p :: i +-> j) :: Constraint

type instance Sat Prof p = Profunctor p
type instance Sat Tight p = Representable p

-- | Runtime witness that every element of a 'Path' satisfies @'Sat' t@. Replaces having a
-- separate witness type per tag (what used to be @SPath@\/@TPath@), so
-- '(Proarrow.Squares.|||)'\/'(Proarrow.Squares.===)' only need one append lemma
-- ('withObAppend'), not one per kind of leg.
type SPath :: Tag -> Path a b -> Type
data SPath t ps where
  SNil :: (CategoryOf k) => SPath t (Nil :: Path k k)
  SCons :: (Sat t p) => SPath t ps -> SPath t (p ::: ps)

-- | @ps@ is a path all of whose elements satisfy @'Sat' t@. Only two cases (@Nil@\/@Cons@)
-- are needed: the head @p@ stays concrete at each step of 'withObAppend'\'s recursion, so
-- GHC's own instance resolution reattaches it to the recursively-derived
-- @'IsOb' t (ps +++ qs)@ for free -- it never needs to reduce @ps +++ qs@ itself, just
-- match the @(':::')@ shape.
class
  (ps +++ Nil ~ ps, forall b c (qs :: Path k b) (rs :: Path b c). Assoc ps qs rs) =>
  IsOb (t :: Tag) (ps :: Path j k)
  where
  singPath :: SPath t ps

instance (CategoryOf k) => IsOb t (Nil :: Path k k) where
  singPath = SNil
instance (Sat t p, IsOb t ps) => IsOb t (p ::: ps) where
  singPath = SCons singPath

-- | Concatenate two witnesses. Plain recursion, no constraint solving -- unlike
-- 'withObAppend', which additionally proves @'IsOb' t (ps +++ qs)@.
appendPath :: SPath t ps -> SPath t qs -> SPath t (ps +++ qs)
appendPath SNil qs = qs
appendPath (SCons ps) qs = SCons (appendPath ps qs)

-- | Bring a specific instantiation of @'IsOb' t ps@\'s quantified @'Assoc' ps qs rs@
-- superclass into scope. Needed explicitly: GHC won't search the superclasses of an
-- arbitrary given constraint to solve an unrelated @~@ goal, so uses of associativity
-- (e.g. in '(Proarrow.Squares.|||)'\/'(Proarrow.Squares.===)') have to ask for it by name
-- at the specific @ps@\/@qs@\/@rs@ in play, even though the fact itself is free once
-- asked for.
withAssoc :: forall ps qs rs t r. (IsOb t ps) => ((Assoc ps qs rs) => r) -> r
withAssoc r = r

-- | A well-formed (horizontal) path: every element is a plain 'Profunctor'.
type IsPath = IsOb Prof

-- | A tight (vertical) path: every element is 'Representable'.
type IsTight = IsOb Tight

-- | A tight path is, in particular, a well-formed path ('Representable' implies
-- 'Profunctor'). Needed explicitly because different 'Tag's don't otherwise know
-- anything about each other.
weakenTight :: SPath Tight ps -> SPath Prof ps
weakenTight SNil = SNil
weakenTight (SCons ps) = SCons (weakenTight ps)

-- | @ps@,@qs@ both satisfy @'Sat' t@ pointwise ⟹ so does @ps +++ qs@.
withObAppend :: forall t ps qs r. (IsOb t qs) => SPath t ps -> ((IsOb t (ps +++ qs)) => r) -> r
withObAppend SNil r = r
withObAppend (SCons ps) r = withObAppend @t @_ @qs ps r

-- | Extract 'Profunctor' evidence for @'Fold' ps@ from a runtime witness.
withFoldOb :: SPath Prof ps -> ((Profunctor (Fold ps)) => r) -> r
withFoldOb SNil r = r
withFoldOb (SCons SNil) r = r
withFoldOb (SCons cs@(SCons _)) r = withFoldOb cs r

-- | Extract 'Representable' evidence for @'Fold' ps@ from a runtime witness. The body is
-- identical to 'withFoldOb'\'s -- both just extract @'Sat' t ('Fold' ps)@, which needs the
-- same single-vs-multi-element case split 'Fold' itself has -- but there's no polymorphic
-- @t@ anywhere that would let one definition serve both: every call site already knows
-- its tag concretely, so there's nothing to be generic over.
withFoldRep :: SPath Tight ps -> ((Representable (Fold ps)) => r) -> r
withFoldRep SNil r = r
withFoldRep (SCons SNil) r = r
withFoldRep (SCons cs@(SCons _)) r = withFoldRep cs r

-- | Combine the composites of two adjacent paths into the composite of their
-- concatenation.
concatFold :: SPath Prof as -> SPath Prof bs -> Fold bs :.: Fold as :~> Fold (as +++ bs)
concatFold SNil bs = withFoldOb bs rightUnitor
concatFold (SCons SNil) bs = case bs of
  SNil -> leftUnitor
  SCons _ -> idN
concatFold (SCons cs@(SCons _)) bs = (concatFold cs bs `o` idN) . associatorInv

-- | The inverse of 'concatFold'.
splitFold :: SPath Prof as -> SPath Prof bs -> Fold (as +++ bs) :~> Fold bs :.: Fold as
splitFold SNil bs = withFoldOb bs rightUnitorInv
splitFold (SCons SNil) bs = case bs of
  SNil -> leftUnitorInv
  SCons _ -> idN
splitFold (SCons cs@(SCons _)) bs = associator . (splitFold cs bs `o` idN)

-- | Apply a 2-cell inside a concatenation, on the right.
whiskerL
  :: SPath Prof xs -> SPath Prof ys -> SPath Prof zs -> Fold ys :~> Fold zs -> Fold (xs +++ ys) :~> Fold (xs +++ zs)
whiskerL xs ys zs f = concatFold xs zs . (f `o` idN) . splitFold xs ys

-- | Apply a 2-cell inside a concatenation, on the left.
whiskerR
  :: SPath Prof xs -> SPath Prof ys -> SPath Prof zs -> Fold xs :~> Fold ys -> Fold (xs +++ zs) :~> Fold (ys +++ zs)
whiskerR xs ys zs f = concatFold ys zs . (idN `o` f) . splitFold xs zs
