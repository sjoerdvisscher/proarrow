{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": @do@ notation, including @rec@ blocks. It exports
-- everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Do where

import Data.Kind (Constraint, Type)
import GHC.TypeNats (Nat, type (+))
import Proarrow.Category.Monoidal (Monoidal, Tensor)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Dialogue (Dialogue)
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal)
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

-- Do notation

-- | A bind in a @do@ block: a term taken apart by a pattern, or the variables of a @rec@ block.
type Bind :: Type -> Type -> Type -> Type -> Type -> Constraint
class Bind k m t cont r | m -> k where
  -- | Bind the right hand side to the pattern of the continuation.
  (>>=) :: m -> (t -> cont) -> r

-- | A term on the right hand side is taken apart by the pattern. Incoherent, so that it is chosen
-- as soon as the right hand side is known, unless the right hand side is a computation.
instance {-# INCOHERENT #-} (BindTerm k t (Term d g a) cont r) => Bind k (Term d g (a :: SYN k)) t cont r where
  {-# INLINE (>>=) #-}
  (>>=) = bindTerm @k @t

-- | A bind of a term, by its pattern. A variable pattern binds a new variable, so that the right
-- hand side is computed once however often the variable is used. The other patterns take the
-- right hand side apart into new variables already.
type BindTerm :: Type -> Type -> Type -> Type -> Type -> Constraint
class BindTerm k t m cont r where
  bindTerm :: m -> (t -> cont) -> r

-- The instances are incoherent, as for patterns: a variable pattern's type is often still unknown
-- when the instance is chosen.

instance
  {-# INCOHERENT #-}
  (Monoidal k, Binds d r a b t cont, Merge r g, r' ~ Term d (Union r g) b)
  => BindTerm k t (Term d g (a :: SYN k)) cont r'
  where
  {-# INLINE bindTerm #-}
  bindTerm (MkTerm m) k = withCtxOb @r (MkTerm (bound @d @r @a @b k . (ctxOb @r M.** m) . merge @r @g))

instance {-# INCOHERENT #-} (BindPat k (Term d g a) (x, y) cont r) => BindTerm k (x, y) (Term d g (a :: SYN k)) cont r where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat k (Term d g a) (x, y, z) cont r)
  => BindTerm k (x, y, z) (Term d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance
  {-# INCOHERENT #-}
  (BindPat k (Term d g a) (w, x, y, z) cont r)
  => BindTerm k (w, x, y, z) (Term d g (a :: SYN k)) cont r
  where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

instance {-# INCOHERENT #-} (BindPat k (Term d g a) () cont r) => BindTerm k () (Term d g (a :: SYN k)) cont r where
  {-# INLINE bindTerm #-}
  bindTerm = bindPat

-- | A computation on the right hand side runs first, and the rest of the block is negative.
instance
  ( Dialogue k
  , KnownObj y
  , Merge g r
  , TyOf @k cont ~ Not y
  , Binds d r a (Not y) t cont
  , r' ~ Term d (Union g r) (Not y)
  )
  => Bind k (Term d g (Not (Not a))) t cont r'
  where
  {-# INLINE (>>=) #-}
  m >>= k = runUp @d @g @r @a @y m (bound @d @r @a @(Not y) k)

-- | The statement of a @rec@ block, whose continuation is its 'return'.
instance
  (Bind k (Term d g a) t cont r', r ~ Ret tt r')
  => Bind k (Term d g (a :: SYN k)) t (Ret tt cont) r
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
class RecVars k t | t -> k where
  type Vars k t :: Ctx k
  recVars :: t

instance (Monoidal k, KnownObj (a :: SYN k)) => RecVars k (Term d '[ '(n, a)] a) where
  {-# INLINE recVars #-}
  type Vars k (Term d '[ '(n, a)] a) = '[ '(n, a)]
  recVars = var @n @a

instance (RecVars k x, RecVars k y) => RecVars k (x, y) where
  {-# INLINE recVars #-}
  type Vars k (x, y) = Union (Vars k x) (Vars k y)
  recVars = (recVars, recVars)

instance (RecVars k x, RecVars k y, RecVars k z) => RecVars k (x, y, z) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z) = Union (Vars k x) (Vars k (y, z))
  recVars = (recVars, recVars, recVars)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w) => RecVars k (x, y, z, w) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w) = Union (Vars k x) (Vars k (y, z, w))
  recVars = (recVars, recVars, recVars, recVars)

instance (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v) => RecVars k (x, y, z, w, v) where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w, v) = Union (Vars k x) (Vars k (y, z, w, v))
  recVars = (recVars, recVars, recVars, recVars, recVars)

instance
  (RecVars k x, RecVars k y, RecVars k z, RecVars k w, RecVars k v, RecVars k u)
  => RecVars k (x, y, z, w, v, u)
  where
  {-# INLINE recVars #-}
  type Vars k (x, y, z, w, v, u) = Union (Vars k x) (Vars k (y, z, w, v, u))
  recVars = (recVars, recVars, recVars, recVars, recVars, recVars)

-- | The variables of a @rec@ block again, at a depth of their own: the rest of the block uses them
-- deeper than the block did. It is asked for both ways, so that what is known about the variables
-- on either side of the block determines the other.
type AnyDepth :: Type -> Type -> Constraint
class AnyDepth t t'

instance (t' ~ Term d' g a) => AnyDepth (Term d g a) t'

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
  :: forall k t d. (Monoidal k, RecVars k t, KnownCtx (Vars k t)) => t -> Ret t (Term d (Vars k t) (Mul (Vars k t)))
return _ = Ret (MkTerm (ctxOb @(Vars k t)))

-- | A @rec@ block before tracing: its body, from its context @g@ to all its variables. Which of them
-- are fed back and which are passed on is only known with the rest of the block, see the 'Bind'
-- instance.
type Rec :: forall {k}. Nat -> Type -> Ctx k -> Type
data Rec d t g where
  Rec :: forall {k} d t (g :: Ctx k). (Interp (Mul g) ~> Interp (Mul (Vars k t))) -> Rec d t g

-- | The body of a @rec@ block, to be traced by the bind after it.
{-# INLINE mfix #-}
mfix :: forall {k} t d (g :: Ctx k). (RecVars k t) => (t -> Ret t (Term d g (Mul (Vars k t)))) -> Rec d t g
mfix f = case unRet (f recVars) of MkTerm body -> Rec body

-- | The rest of the @do@ block after a @rec@ block, which traces it. The variables of the block
-- that the block itself uses are fed back, the ones the rest uses are passed on, a variable that
-- both use is copied, and one that neither uses is discarded. The rest gets the variables anew,
-- with the same ids, so that it can use them at its own depth.
instance
  ( TracedMonoidal k
  , RecVars k t
  , AnyDepth t t'
  , AnyDepth t' t
  , RecVars k t'
  , cont ~ Term (HeadId (Vars k t) + 1) (CtxOf @k cont) (TyOf @k cont)
  , r ~ Term d (Union (Minus (CtxOf @k cont) (Vars k t)) (Minus g (Vars k t))) (TyOf @k cont)
  , Unmerge (Inter g (Vars k t)) (Minus g (Vars k t))
  , Union (Inter g (Vars k t)) (Minus g (Vars k t)) ~ g
  , Thin (Vars k t) (Union (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)))
  , Merge (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t))
  , Merge (Minus (CtxOf @k cont) (Vars k t)) (Minus g (Vars k t))
  , Unmerge (Minus (CtxOf @k cont) (Vars k t)) (Inter (CtxOf @k cont) (Vars k t))
  , Union (Minus (CtxOf @k cont) (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)) ~ CtxOf @k cont
  )
  => Bind k (Rec d t (g :: Ctx k)) t' cont r
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
                            . unmerge @(Minus (CtxOf @k cont) (Vars k t)) @(Inter (CtxOf @k cont) (Vars k t))
                            . ( ctxOb @(Minus (CtxOf @k cont) (Vars k t))
                                  M.** coact
                                    @Tensor
                                    @(~>)
                                    @(Interp (Mul (Inter g (Vars k t))))
                                    @(Interp (Mul (Minus g (Vars k t))))
                                    @(Interp (Mul (Inter (CtxOf @k cont) (Vars k t))))
                                    ( merge @(Inter g (Vars k t)) @(Inter (CtxOf @k cont) (Vars k t))
                                        . thin @(Vars k t) @(Union (Inter g (Vars k t)) (Inter (CtxOf @k cont) (Vars k t)))
                                        . body
                                        . unmerge @(Inter g (Vars k t)) @(Minus g (Vars k t))
                                    )
                              )
                            . merge @(Minus (CtxOf @k cont) (Vars k t)) @(Minus g (Vars k t))
                        )
                    )
                )
            )
        )

-- | GHC's translation of @rec@ refers to @fail@, but pairs of variables always match.
fail :: a
fail = P.error "Proarrow.Tools.SMC.fail: a pattern did not match"
