{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": @do@ notation, including @rec@ blocks. It exports
-- everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Do where

import Data.Kind (Constraint, Type)
import GHC.TypeNats (Nat, type (+))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor, SymMonoidal, Tensor)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..))
import Proarrow.Category.Monoidal.Strength (Costrong (..))
import Proarrow.Core (CAT, Hom, Profunctor (..), Promonad (..))
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

-- Do notation

-- | A bind in a @do@ block: a term taken apart by a pattern, or the variables of a @rec@ block.
type Bind :: forall {k}. CAT k -> Type -> Type -> Type -> Type -> Constraint
class Bind p m t cont r | m -> p where
  -- | Bind the right hand side to the pattern of the continuation.
  (>>=) :: m -> (t -> cont) -> r

-- | A term on the right hand side is taken apart by the pattern. Incoherent, so that it is chosen
-- as soon as the right hand side is known, unless the right hand side is a computation.
instance {-# INCOHERENT #-} (BindTerm p t (TermP p d g a) cont r) => Bind p (TermP p d g (a :: SYN k)) t cont r where
  {-# INLINE (>>=) #-}
  (>>=) = bindTerm @p @t

-- | A bind of a term, by its pattern. A variable pattern binds a new variable, so that the right
-- hand side is computed once however often the variable is used. The other patterns take the
-- right hand side apart into new variables already.
type BindTerm :: forall {k}. CAT k -> Type -> Type -> Type -> Type -> Constraint
class BindTerm p t m cont r where
  bindTerm :: m -> (t -> cont) -> r

-- The instances are incoherent, as for patterns: a variable pattern's type is often still unknown
-- when the instance is chosen.

instance
  {-# INCOHERENT #-}
  (Promonad p, MonoidalProfunctor p, Binds p d r a b t cont, Merge r g, r' ~ TermP p d (Union r g) b)
  => BindTerm p t (TermP p d g (a :: SYN k)) cont r'
  where
  {-# INLINE bindTerm #-}
  bindTerm (MkTerm m) k =
    withCtxOb @r (MkTerm (bound @p @d @r @a @b k . lmap (merge @r @g) (id @p @(Interp (Mul r)) M.** m)))

instance
  {-# INCOHERENT #-}
  (BindPat p (TermP p d g a) (x, y) cont r)
  => BindTerm p (x, y) (TermP p d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat p (TermP p d g a) (x, y, z) cont r)
  => BindTerm p (x, y, z) (TermP p d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat p (TermP p d g a) (w, x, y, z) cont r)
  => BindTerm p (w, x, y, z) (TermP p d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat p (TermP p d g a) (v, w, x, y, z) cont r)
  => BindTerm p (v, w, x, y, z) (TermP p d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat p (TermP p d g a) (u, v, w, x, y, z) cont r)
  => BindTerm p (u, v, w, x, y, z) (TermP p d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat p (TermP p d g a) () cont r)
  => BindTerm p () (TermP p d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

-- An explicit consumer determines what it consumes. An embedded dual object instead
-- uses the negative result expected by the surrounding computation.
type Negative :: forall {k}. SYN k -> SYN k -> Constraint
class (Interp c ~ Dual (Interp y)) => Negative c y

instance (y ~ y') => Negative (Not y') y
instance (f ~ Dual (Interp y)) => Negative (F f) y

-- | A computation on the right hand side runs first, and the rest of the block is negative.
instance
  ( p ~ Hom k
  , Dialogue k
  , KnownObj y
  , Merge g r
  , Negative (TyOf @k cont) y
  , Binds p d r a (TyOf @k cont) t cont
  , r' ~ TermP p d (Union g r) (Not y)
  )
  => Bind p (TermP p d g (Not (Not a) :: SYN k)) t cont r'
  where
  {-# INLINE (>>=) #-}
  m >>= k = runUp @d @g @r @a @y m (bound @p @d @r @a @(TyOf @k cont) k)

-- | The statement of a @rec@ block, whose continuation is its 'return'.
instance
  (Bind p (TermP p d g a) t cont r', r ~ Ret tt r')
  => Bind p (TermP p d g (a :: SYN k)) t (Ret tt cont) r
  where
  {-# INLINE (>>=) #-}
  x >>= k = Ret (x >>= \p -> unRet (k p))

-- | The body of a @rec@ block, tagged with the tuple of its variables. GHC's translation passes
-- that tuple to both 'return' and 'mfix', and this tag is what makes them the same.
type Ret :: Type -> Type -> Type
newtype Ret t x = Ret x

unRet :: Ret t x -> x
unRet (Ret x) = x

-- | The variables of a @rec@ block, as GHC tuples them up.
type RecVars :: Type -> Type -> Constraint
-- The empty tuple contains no term from which to recover the category.
class RecVars k t where
  type Vars k t :: Ctx k
  recVars :: t

instance RecVars k () where
  type Vars k () = '[]
  {-# INLINE recVars #-}
  recVars = ()

instance (Promonad p, KnownObj (a :: SYN k)) => RecVars k (TermP (p :: CAT k) d '[ '(n, a)] a) where
  {-# INLINE recVars #-}
  type Vars k (TermP p d '[ '(n, a)] a) = '[ '(n, a)]
  recVars = var @n @a

instance (RecVars k x, RecVars k y) => RecVars k (x, y) where
  {-# INLINE recVars #-}
  type Vars k (x, y) = Union (Vars k x) (Vars k y)
  recVars = (recVars @k, recVars @k)

instance (RecVars k x, RecVars k y, RecVars k z) => RecVars k (x, y, z) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z) = Union (Vars k x) (Vars k (y, z))
  recVars = (recVars @k, recVars @k, recVars @k)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w) => RecVars k (x, y, z, w) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w) = Union (Vars k x) (Vars k (y, z, w))
  recVars = (recVars @k, recVars @k, recVars @k, recVars @k)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v) => RecVars k (x, y, z, w, v) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w, v) = Union (Vars k x) (Vars k (y, z, w, v))
  recVars = (recVars @k, recVars @k, recVars @k, recVars @k, recVars @k)

instance
  (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v, RecVars k u)
  => RecVars k (x, y, z, w, v, u)
  where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w, v, u) = Union (Vars k x) (Vars k (y, z, w, v, u))
  recVars = (recVars @k, recVars @k, recVars @k, recVars @k, recVars @k, recVars @k)

-- | The variables of a @rec@ block again, at a depth of their own: the rest of the block uses them
-- deeper than the block did. It is asked for both ways, so that what is known about the variables
-- on either side of the block determines the other.
type AnyDepth :: Type -> Type -> Constraint
class AnyDepth t t'

instance (t' ~ ()) => AnyDepth () t'

instance (t' ~ TermP p d' g a) => AnyDepth (TermP p d g a) t'

instance (AnyDepth x x', AnyDepth y y', t' ~ (x', y')) => AnyDepth (x, y) t'

instance (AnyDepth x x', AnyDepth y y', AnyDepth z z', t' ~ (x', y', z')) => AnyDepth (x, y, z) t'

instance (AnyDepth x x', AnyDepth y y', AnyDepth z z', AnyDepth w w', t' ~ (x', y', z', w')) => AnyDepth (x, y, z, w) t'

instance
  (AnyDepth x x', AnyDepth y y', AnyDepth z z', AnyDepth w w', AnyDepth v v', t' ~ (x', y', z', w', v'))
  => AnyDepth (x, y, z, w, v) t'

instance
  ( AnyDepth x x'
  , AnyDepth y y'
  , AnyDepth z z'
  , AnyDepth w w'
  , AnyDepth v v'
  , AnyDepth u u'
  , t' ~ (x', y', z', w', v', u')
  )
  => AnyDepth (x, y, z, w, v, u) t'

-- | The end of a @rec@ block: all its variables, as the tensor of their context.
{-# INLINE return #-}
return
  :: forall k t d (p :: CAT k)
   . (Monoidal k, Promonad p, RecVars k t, KnownCtx (Vars k t))
  => t -> Ret t (TermP p d (Vars k t) (Mul (Vars k t)))
return _ = withCtxOb @(Vars k t) (Ret (MkTerm (id @p @(Interp (Mul (Vars k t))))))

-- | A @rec@ block before tracing: its body, from its context @g@ to all its variables. Which of them
-- are fed back and which are passed on is only known with the rest of the block, see the 'Bind'
-- instance.
type Rec :: forall {k}. CAT k -> Nat -> Type -> Ctx k -> Type
data Rec p d t g where
  Rec :: forall {k} (p :: CAT k) d t (g :: Ctx k). p (Interp (Mul g)) (Interp (Mul (Vars k t))) -> Rec p d t g

-- | The body of a @rec@ block, to be traced by the bind after it.
{-# INLINE mfix #-}
mfix
  :: forall {k} t d (g :: Ctx k) (p :: CAT k). (RecVars k t) => (t -> Ret t (TermP p d g (Mul (Vars k t)))) -> Rec p d t g
mfix f = case unRet (f (recVars @k @t)) of MkTerm body -> Rec body

-- The continuation stays at the same depth if GHC retains no variables of the block.
type RecDepth :: forall {k}. Nat -> Ctx k -> Nat
type family RecDepth d g where
  RecDepth d '[] = d
  RecDepth d ('(n, a) ': g) = n + 1

-- | The rest of the @do@ block after a @rec@ block, which traces it. The variables of the block
-- that the block itself uses are fed back, the ones the rest uses are passed on, a variable that
-- both use is copied, and one that neither uses is discarded. The rest gets the variables anew,
-- with the same ids, so that it can use them at its own depth.
instance
  ( Promonad p
  , MonoidalProfunctor p
  , Costrong Tensor p
  , SymMonoidal k
  , RecVars k t
  , AnyDepth t t'
  , AnyDepth t' t
  , RecVars k t'
  , cont ~ TermP p (RecDepth d (Vars k t)) (CtxOf @k cont) (TyOf @k cont)
  , r ~ TermP p d (Union (Minus (CtxOf @k cont) (Vars k t)) (Minus g (Vars k t))) (TyOf @k cont)
  , Unmerge (Inter g (Vars k t)) (Minus g (Vars k t))
  , Union (Inter g (Vars k t)) (Minus g (Vars k t)) ~ g
  , Thin (Vars k t) (Union (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)))
  , Merge (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t))
  , Merge (Minus (CtxOf @k cont) (Vars k t)) (Minus g (Vars k t))
  , Unmerge (Minus (CtxOf @k cont) (Vars k t)) (Inter (CtxOf @k cont) (Vars k t))
  , Union (Minus (CtxOf @k cont) (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)) ~ CtxOf @k cont
  )
  => Bind p (Rec p d t (g :: Ctx k)) t' cont r
  where
  {-# INLINE (>>=) #-}
  Rec body >>= k = case k (recVars @k @t') of
    MkTerm rest ->
      withCtxOb @(Minus (CtxOf @k cont) (Vars k t))
        ( withCtxOb @(Inter g (Vars k t))
            ( withCtxOb @(Minus g (Vars k t))
                ( withCtxOb @(Inter (CtxOf @k cont) (Vars k t))
                    ( MkTerm
                        ( rest
                            . dimap
                              (merge @(Minus (CtxOf @k cont) (Vars k t)) @(Minus g (Vars k t)))
                              (unmerge @(Minus (CtxOf @k cont) (Vars k t)) @(Inter (CtxOf @k cont) (Vars k t)))
                              ( id @p @(Interp (Mul (Minus (CtxOf @k cont) (Vars k t))))
                                  M.** coact
                                    @Tensor
                                    @p
                                    @(Interp (Mul (Inter g (Vars k t))))
                                    @(Interp (Mul (Minus g (Vars k t))))
                                    @(Interp (Mul (Inter (CtxOf @k cont) (Vars k t))))
                                    ( dimap
                                        (unmerge @(Inter g (Vars k t)) @(Minus g (Vars k t)))
                                        ( merge @(Inter g (Vars k t)) @(Inter (CtxOf @k cont) (Vars k t))
                                            . thin @(Vars k t) @(Union (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)))
                                        )
                                        body
                                    )
                              )
                        )
                    )
                )
            )
        )

-- | GHC's translation of @rec@ refers to @fail@, but pairs of variables always match.
fail :: a
fail = P.error "Proarrow.Tools.SMC.fail: a pattern did not match"
