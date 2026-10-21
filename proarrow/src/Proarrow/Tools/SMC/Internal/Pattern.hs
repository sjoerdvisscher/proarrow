{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": patterns and binders. It exports everything, also what
-- the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Pattern where

import Data.Kind (Constraint, Type)
import GHC.TypeNats (Nat, type (+))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..), bindDual)
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..), obj)
import Prelude (type (~))

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

-- | Compile a function on terms to a morphism. The function receives the input through a pattern
-- (see /Patterns/), so @()@ compiles a term without inputs and a tuple takes a tensor apart.
{-# INLINE toSMC #-}
toSMC
  :: forall {k} (a :: SYN k) b t cont
   . (Monoidal k, Binds (~>) 0 '[] a b t cont)
  => (t -> cont)
  -> Interp a ~> Interp b
toSMC = proc @a @b

-- | Compile a function on terms to an arrow of the promonad @p@, as 'toSMC' does for the morphisms
-- of the category, which are the case @p = ('~>')@. The terms' computations are arrows of @p@,
-- lifted with '(-<)' or 'lift', and run in the order they are written; variables are values,
-- which the category's structure copies and discards. This mirrors @proc@ in Haskell's arrow
-- notation, whose @Arrows@ extension must be disabled.
{-# INLINE proc #-}
proc
  :: forall {k} (a :: SYN k) b t cont (p :: CAT k)
   . (MonoidalProfunctor p, Binds p 0 '[] a b t cont)
  => (t -> cont)
  -> p (Interp a) (Interp b)
proc k = withSynOb @a (lmap (leftUnitorInv @k @(Interp a)) (bound @p @0 @'[] @a @b k))

-- | Lift an arrow onto a term or tuple of terms, with its result embedded by 'F'.
-- The result object is inferred from the arrow. Use 'lift' for composite result syntax.
{-# INLINE liftF #-}
liftF
  :: forall {k} (a :: SYN k) b t (p :: CAT k) d
   . (Promonad p, Tuple p t a)
  => p (Interp a) b -> t -> TermP p d (TupleCtx k t) (F b)
liftF f t = lift @a @(F b) f (tuple @p t)

infixr 0 -<

-- | Arrow application, mirroring @f -< x@ in Haskell's arrow notation.
-- This is infix 'liftF': the input may be a term or tuple, and the result is embedded by 'F'.
-- The @Arrows@ extension must be disabled, since it reserves this symbol.
{-# INLINE (-<) #-}
(-<)
  :: forall {k} (a :: SYN k) b t (p :: CAT k) d
   . (Promonad p, Tuple p t a)
  => p (Interp a) b -> t -> TermP p d (TupleCtx k t) (F b)
(-<) = liftF @a @b

-- | The identity morphism, named as in Haskell's arrow notation.
-- An alias for 'Proarrow.Core.id'; @returnA -< x@ embeds the input by 'F'.
{-# INLINE returnA #-}
returnA :: (Promonad p, Ob a) => p a a
returnA = id

-- | The shift of a positive type to a negative one: a computation that produces an @a@. A term of
-- it is a consumer of consumers of @a@, so in a category with @'Dual' a = a ~~> r@ it is the
-- continuation passing type @(a -> r) -> r@.
type Up :: forall {k}. SYN k -> SYN k
type Up a = Not (Not a)

-- | Run a computation against the rest of a block. The body is what the rest does with the value,
-- given the context @r@; it becomes a consumer of the computation, whose context @g@ joins. What
-- the binds of a computation share, the counterpart of 'bound'.
{-# INLINE runUp #-}
runUp
  :: forall {k} d g r (a :: SYN k) y
   . (Dialogue k, KnownObj a, KnownObj y, Merge g r)
  => Term d g (Up a)
  -> (Interp (Mul r) ** Interp a ~> Interp (Not y))
  -> Term d (Union g r) (Not y)
runUp (MkTerm m) body =
  withCtxOb @r
    ( withSynOb @a
        ( withSynOb @y
            ( MkTerm
                ( bindDual @(Interp (Mul r)) @(Interp a) @(Interp y) body
                    . (m M.** obj @(Interp (Mul r)))
                    . merge @g @r
                )
            )
        )
    )

-- | A value as the computation that produces it: double negation introduction, and the return of
-- a @do@ block in the continuation reading. It also reads as a producer of @a@ handed over as a
-- consumer of @'Not' a@. The value can be given as a 'Tuple' of terms, built by the type expected.
{-# INLINE ret #-}
ret
  :: forall {k} {p} (a :: SYN k) t d
   . (Dialogue k, Profunctor p, KnownObj a, Tuple p t a)
  => t -> TermP p d (TupleCtx k t) (Up a)
ret t = withSynOb @a (rmapT (doubleNegInv @k @(Interp a)) (tuple @p @t @a t))

-- | A term built from a tuple of terms, by the type it is expected to have: a term is itself, a
-- pair at a tensor is the tensor of its parts, and a pair at a computation @'Up' a@ is the
-- computation of the pair at @a@. A tuple of three to six stands for pairs nested to the left, as in
-- patterns. The parts may come from different binding depths; the result adopts the depth
-- where it is used, and their contexts are merged.
type Tuple :: forall {k}. CAT k -> Type -> SYN k -> Constraint
class Tuple (p :: CAT k) t a where
  tuple :: t -> TermP p d (TupleCtx k t) a

-- | The context of a tuple of terms: the union of the contexts of its parts.
type TupleCtx :: forall k -> Type -> Ctx k
type family TupleCtx k t where
  TupleCtx k (x, y) = Union (TupleCtx k x) (TupleCtx k y)
  TupleCtx k (x, y, z) = TupleCtx k ((x, y), z)
  TupleCtx k (w, x, y, z) = TupleCtx k ((w, x, y), z)
  TupleCtx k (v, w, x, y, z) = TupleCtx k ((v, w, x, y), z)
  TupleCtx k (u, v, w, x, y, z) = TupleCtx k ((u, v, w, x, y), z)
  TupleCtx k t = CtxOf @k t

-- The generic instances are incoherent, as for patterns: a term's type is often still unknown when
-- the instance is chosen, and a pair defaults to a tensor until its type is known to be an 'Up'.

-- | A term keeps its context and type, adapting to the depth where it is used.
-- Variable ids in the context are unchanged.
instance {-# INCOHERENT #-} (t ~ TermP p d g a) => Tuple p t a where
  {-# INLINE tuple #-}
  tuple t = recast t

-- | A pair at a tensor is the tensor of its parts.
instance
  {-# INCOHERENT #-}
  ( MonoidalProfunctor p
  , a ~ (a1 :** a2)
  , Tuple p x a1
  , Tuple p y a2
  , Merge (TupleCtx k x) (TupleCtx k y)
  )
  => Tuple p (x, y) (a :: SYN k)
  where
  {-# INLINE tuple #-}
  tuple (x, y) = tuple @p @x @a1 x ** tuple @p @y @a2 y

-- | A pair at a computation is the computation of the pair at the value.
instance (Dialogue k, Profunctor p, KnownObj a, Tuple p (x, y) a) => Tuple p (x, y) (Not (Not a) :: SYN k) where
  {-# INLINE tuple #-}
  tuple p = ret @a p

instance (Tuple p ((x, y), z) a) => Tuple p (x, y, z) a where
  {-# INLINE tuple #-}
  tuple (x, y, z) = tuple @p @((x, y), z) @a ((x, y), z)

instance (Tuple p ((w, x, y), z) a) => Tuple p (w, x, y, z) a where
  {-# INLINE tuple #-}
  tuple (w, x, y, z) = tuple @p @((w, x, y), z) @a ((w, x, y), z)

instance (Tuple p ((v, w, x, y), z) a) => Tuple p (v, w, x, y, z) a where
  {-# INLINE tuple #-}
  tuple (v, w, x, y, z) = tuple @p @((v, w, x, y), z) @a ((v, w, x, y), z)

instance (Tuple p ((u, v, w, x, y), z) a) => Tuple p (u, v, w, x, y, z) a where
  {-# INLINE tuple #-}
  tuple (u, v, w, x, y, z) = tuple @p @((u, v, w, x, y), z) @a ((u, v, w, x, y), z)

-- | The pattern @t@ of a binder: it takes apart the variable @(n, a)@, and the binder's body
-- @cont@ then gives a term at depth @n + 1@ with type @b@, whose context is @g@ and possibly that
-- variable. Both the variable's type and the rest of the context must be known.
type Binds :: forall {k}. CAT k -> Nat -> Ctx k -> SYN k -> SYN k -> Type -> Type -> Constraint
class (KnownObj a, KnownCtx g) => Binds p n g (a :: SYN k) b t cont where
  -- | The body of a binder, with the pattern taking apart its new variable, as a morphism from the
  -- context around it and the variable. This is what 'toSMC', 'Proarrow.Tools.SMC.lam',
  -- 'Proarrow.Tools.SMC.loop', 'Proarrow.Tools.SMC.cont', 'Proarrow.Tools.SMC.caseOf',
  -- 'Proarrow.Tools.SMC.sumOver' and the binds of @do@ notation share.
  bound :: (t -> cont) -> p (Interp (Mul g) ** Interp a) (Interp b)

-- The context of the body is @g'@, which only the instance needs to name.
instance
  ( Promonad p
  , KnownObj a
  , KnownCtx g
  , BindPat p (TermP p (n + 1) '[ '(n, a)] a) t cont (TermP p (n + 1) g' b)
  , BindVar n a g' g
  )
  => Binds p n g (a :: SYN k) b t cont
  where
  {-# INLINE bound #-}
  bound k =
    case bindPat @p @(TermP p (n + 1) '[ '(n, a)] a) @t @cont @(TermP p (n + 1) g' b) (var @n @a @(n + 1) @p) k of
      MkTerm body -> lmap (bindVar @n @a @g' @g) body

-- | A term on the right hand side taken apart by the pattern of the continuation. The types of the
-- continuation and the result are matched with equalities, so that the instance is chosen as soon
-- as the right hand side is known.
type BindPat :: forall {k}. CAT k -> Type -> Type -> Type -> Type -> Constraint
class BindPat p m t cont r | m -> p where
  bindPat :: m -> (t -> cont) -> r

instance
  ( cont ~ TermP p (d + PSize t) (CtxOf @k cont) (TyOf @k cont)
  , r ~ TermP p d gr (TyOf @k cont)
  , Pat p t d g a (CtxOf @k cont) (TyOf @k cont) gr
  )
  => BindPat p (TermP p d g (a :: SYN k)) t cont r
  where
  {-# INLINE bindPat #-}
  bindPat = pat @p @t @d @g @a @(CtxOf @k cont) @(TyOf @k cont) @gr

-- | A pattern: a variable, @()@, or a pair of patterns. A tuple of three to six stands for pairs
-- nested to the left, as @a ':**' b ':**' c@ is: @(x, y, z)@ is @((x, y), z)@. Binding it at depth
-- @d@ to a term with context @g@ and type @a@, with a continuation with context @g'@ and type @c@,
-- gives a term with context @gr@, which each instance fixes. A pair or @()@ at a computation,
-- @'Up' a@, runs it and matches its value, so @c@ is then negative.
type Pat :: forall {k}. CAT k -> Type -> Nat -> Ctx k -> SYN k -> Ctx k -> SYN k -> Ctx k -> Constraint
class Pat p t d g a g' c gr where
  pat :: TermP p d g a -> (t -> TermP p (d + PSize t) g' c) -> TermP p d gr c

-- | The number of variables a pattern binds on the way, and so the depth it adds.
type PSize :: Type -> Nat
type family PSize t where
  PSize (x, y) = 2 + PSize x + PSize y
  PSize (x, y, z) = PSize ((x, y), z)
  PSize (w, x, y, z) = PSize ((w, x, y), z)
  PSize (v, w, x, y, z) = PSize ((v, w, x, y), z)
  PSize (u, v, w, x, y, z) = PSize ((u, v, w, x, y), z)
  PSize t = 0

-- The generic instances are incoherent: a variable pattern's type is often still unknown when the
-- instance is chosen, and a pair pattern's type is always a pair by then. The instances at a
-- computation are more specific, so they win once the type is known to be an 'Up'.

-- | The pattern @()@ at a computation of the unit runs it.
instance
  (p ~ Hom k, Dialogue k, KnownObj y, c ~ Not y, Merge g g', gr ~ Union g g')
  => Pat p () d g (Not (Not I) :: SYN k) g' c gr
  where
  {-# INLINE pat #-}
  pat u k = case k () of
    MkTerm t -> runUp @d @g @g' @I @y u (withCtxOb @g' (t . rightUnitor @k @(Interp (Mul g'))))

-- | A pair pattern at a computation runs it and takes its value apart. The value needs no variable
-- of its own: the pattern's variables take the ids it would have taken.
instance
  ( p ~ Hom k
  , Dialogue k
  , KnownObj a
  , KnownObj y
  , c ~ Not y
  , Pat p (x, y') d '[ '(d, a)] a g' c gp
  , BindVar d a gp r
  , Merge g r
  , gr ~ Union g r
  )
  => Pat p (x, y') d g (Not (Not a) :: SYN k) g' c gr
  where
  {-# INLINE pat #-}
  pat m k = case pat @p @(x, y') @d @'[ '(d, a)] @a @g' @c @gp (var @d @a @d) k of
    MkTerm body -> runUp @d @g @r @a @y m (body . bindVar @d @a @gp @r)

-- | The pattern @()@ uses up a term of the unit type.
instance
  {-# INCOHERENT #-}
  (MonoidalProfunctor p, a ~ I, KnownObj c, Merge g g', gr ~ Union g g')
  => Pat p () d g (a :: SYN k) g' c gr
  where
  {-# INLINE pat #-}
  pat (MkTerm u) k = case k () of
    MkTerm t -> withSynOb @c (MkTerm (dimap (merge @g @g') (leftUnitor @k @(Interp c)) (u M.** t)))

-- | A variable pattern names the right hand side, which is always a variable. If the body does not
-- use it, the binder discards it.
instance {-# INCOHERENT #-} (t ~ TermP p (DepthOf t) g a, gr ~ g') => Pat p t d g a g' c gr where
  {-# INLINE pat #-}
  pat x k = k (recast x)

-- | A pair pattern at an embedded tensor exposes its two embedded components.
-- The tensor pattern supplies the binding and context operations.
instance
  ( a ~ (a1 ** a2)
  , Pat p (x, y) d g (F a1 :** F a2) g' c gr
  )
  => Pat p (x, y) d g (F (a :: k)) g' c gr
  where
  {-# INLINE pat #-}
  pat (MkTerm f) k = pat @p @(x, y) @d @g @(F a1 :** F a2) (MkTerm f) k

instance
  {-# INCOHERENT #-}
  ( Promonad p
  , MonoidalProfunctor p
  , a ~ (a1 :** a2)
  , KnownObj a1
  , KnownObj a2
  , Pat p y (d + 2 + PSize x) '[ '(d + 1, a2)] a2 g' c gy
  , Pat p x (d + 2) '[ '(d, a1)] a1 gy c gxy
  , d + 2 + PSize x + PSize y ~ d + PSize (x, y)
  , BindVar (d + 1) a2 gxy r1
  , BindVar d a1 r1 r
  , Merge r g
  , gr ~ Union r g
  )
  => Pat p (x, y) d g (a :: SYN k) g' c gr
  where
  {-# INLINE pat #-}
  pat s k =
    split @d @g @gxy @r1 @r
      s
      ( \a b ->
          pat @p @x @(d + 2) @'[ '(d, a1)] @a1 @gy @c @gxy
            a
            (\px -> pat @p @y @(d + 2 + PSize x) @'[ '(d + 1, a2)] @a2 @g' @c @gy b (\py -> k (px, py)))
      )

instance {-# INCOHERENT #-} (Pat p ((x, y), z) d g a g' c gr) => Pat p (x, y, z) d g a g' c gr where
  {-# INLINE pat #-}
  pat s k = pat @p @((x, y), z) @d @g @a @g' @c @gr s (\((px, py), pz) -> k (px, py, pz))

instance {-# INCOHERENT #-} (Pat p ((w, x, y), z) d g a g' c gr) => Pat p (w, x, y, z) d g a g' c gr where
  {-# INLINE pat #-}
  pat s k = pat @p @((w, x, y), z) @d @g @a @g' @c @gr s (\((pw, px, py), pz) -> k (pw, px, py, pz))

instance {-# INCOHERENT #-} (Pat p ((v, w, x, y), z) d g a g' c gr) => Pat p (v, w, x, y, z) d g a g' c gr where
  {-# INLINE pat #-}
  pat s k = pat @p @((v, w, x, y), z) @d @g @a @g' @c @gr s (\((pv, pw, px, py), pz) -> k (pv, pw, px, py, pz))

instance
  {-# INCOHERENT #-}
  (Pat p ((u, v, w, x, y), z) d g a g' c gr)
  => Pat p (u, v, w, x, y, z) d g a g' c gr
  where
  {-# INLINE pat #-}
  pat s k =
    pat @p @((u, v, w, x, y), z) @d @g @a @g' @c @gr
      s
      (\((pu, pv, pw, px, py), pz) -> k (pu, pv, pw, px, py, pz))
