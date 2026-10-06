{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": the contexts of terms, and the operations on them that
-- reorder, copy and discard variables. It exports everything, also what the public module keeps
-- hidden.
module Proarrow.Tools.SMC.Internal.Context where

import Data.Kind (Constraint, Type)
import GHC.TypeNats (CmpNat, Nat)
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , SymMonoidal (..)
  , associator'
  , associatorInv'
  , rightUnitorWith
  , swapInner
  )
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..))
import Proarrow.Object (Obj)
import Prelude (Ordering (..), type (~))

import Proarrow.Tools.SMC.Internal.Syntax

-- | A context: the variables a term uses, each with its id and type, by descending id.
type Ctx :: Type -> Type
type Ctx k = [(Nat, SYN k)]

-- | The type standing in for a context: the tensor of its variables' types, with the most
-- recently bound variable on the right. A single variable is just its type, so a variable is the
-- identity. The cost is that @Mul ('(n, a) ': g)@ only reduces once @g@ is known to be empty or
-- not, which 'ctxCase' tells.
type Mul :: forall {k}. Ctx k -> SYN k
type family Mul g where
  Mul '[] = I
  Mul '[ '(n, a)] = a
  Mul ('(n, a) ': g) = Mul g :** a

-- | A context that is known to be empty or not, all the way down.
type KnownCtx :: forall {k}. Ctx k -> Constraint
class KnownCtx (g :: Ctx k) where
  -- | Case analysis on the context, which is what lets @'Mul' ('(n, a) ': g)@ reduce.
  ctxCase :: ((g ~ '[]) => r) -> (forall n a g'. (g ~ ('(n, a) ': g'), KnownObj a, KnownCtx g') => r) -> r

  -- | The tensor of a context is an object. A method rather than a function over 'ctxCase', so that
  -- at a known context it is not recursive and can be inlined.
  withCtxOb :: (Monoidal k) => ((Ob (Interp (Mul g))) => r) -> r

instance KnownCtx ('[] :: Ctx k) where
  {-# INLINE ctxCase #-}
  {-# INLINE withCtxOb #-}
  ctxCase e _ = e
  withCtxOb r = r

instance (KnownObj a, KnownCtx g) => KnownCtx ('(n, a) ': g) where
  {-# INLINE ctxCase #-}
  {-# INLINE withCtxOb #-}
  ctxCase _ c = c
  withCtxOb r = ctxCase @g (withSynOb @a r) (withCtxOb @g (withSynOb @a (withOb2 @_ @(Interp (Mul g)) @(Interp a) r)))

-- | The identity on the tensor of a context.
{-# INLINE ctxOb #-}
ctxOb :: forall {k} (g :: Ctx k). (Monoidal k, KnownCtx g) => Obj (Interp (Mul g))
ctxOb = withCtxOb @g (obj @(Interp (Mul g)))

-- | A new variable on the right of a context: a unitor if the context was empty, and nothing
-- otherwise.
{-# INLINE snoc #-}
snoc
  :: forall {k} n (a :: SYN k) g
   . (Monoidal k, KnownObj a, KnownCtx g) => Interp (Mul g) ** Interp a ~> Interp (Mul ('(n, a) ': g))
snoc = ctxCase @g (withSynOb @a leftUnitor) (ctxOb @('(n, a) ': g))

-- | The context of two terms used side by side.
type Union :: forall {k}. Ctx k -> Ctx k -> Ctx k
type family Union g1 g2 where
  Union '[] g2 = g2
  Union g1 '[] = g1
  Union ('(n, a) ': g1) ('(m, b) ': g2) = UnionBy (CmpNat n m) ('(n, a) ': g1) ('(m, b) ': g2)

type UnionBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Ctx k
type family UnionBy o g1 g2 where
  UnionBy GT (x ': g1) g2 = x ': Union g1 g2
  UnionBy LT g1 (y ': g2) = y ': Union g1 g2
  UnionBy EQ (x ': g1) (y ': g2) = x ': Union g1 g2

-- | The newest variable split off the tensor of a context, the inverse of 'snoc'.
{-# INLINE unsnoc #-}
unsnoc
  :: forall {k} n (a :: SYN k) g
   . (Monoidal k, KnownObj a, KnownCtx g) => Interp (Mul ('(n, a) ': g)) ~> Interp (Mul g) ** Interp a
unsnoc = ctxCase @g (withSynOb @a leftUnitorInv) (ctxOb @('(n, a) ': g))

-- | Split the tensor of the union of two contexts into the tensors of the two contexts. This is
-- where the wires are reordered, the only place 'swap' is used, and where a variable that both
-- contexts have is copied.
type Merge :: forall {k}. Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => Merge (g1 :: Ctx k) g2 where
  merge :: Interp (Mul (Union g1 g2)) ~> Interp (Mul g1) ** Interp (Mul g2)

instance (Monoidal k, KnownCtx g2) => Merge ('[] :: Ctx k) g2 where
  {-# INLINE merge #-}
  merge = withCtxOb @g2 leftUnitorInv

instance (Monoidal k, KnownCtx ('(n, a) ': g1)) => Merge ('(n, a) ': g1 :: Ctx k) '[] where
  {-# INLINE merge #-}
  merge = withCtxOb @('(n, a) ': g1) rightUnitorInv

instance
  ( Monoidal k
  , KnownObj a
  , KnownObj b
  , KnownCtx g1
  , KnownCtx g2
  , MergeBy (CmpNat n m) ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  )
  => Merge ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  where
  {-# INLINE merge #-}
  merge = mergeBy @(CmpNat n m) @('(n, a) ': g1) @('(m, b) ': g2)

-- | 'merge' for two non-empty contexts, by which of the two has the larger head id.
type MergeBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => MergeBy o (g1 :: Ctx k) g2 where
  mergeBy :: Interp (Mul (UnionBy o g1 g2)) ~> Interp (Mul g1) ** Interp (Mul g2)

-- The union of two non-empty contexts is not empty, so its tensor splits off the newest variable
-- as is, which the equality says for GHC. If the newest variable is alone on its side, merging is
-- one swap or nothing.
instance
  ( SymMonoidal k
  , Merge g1 ('(m, b) ': g2)
  , KnownObj (a :: SYN k)
  , KnownObj b
  , Mul ('(n, a) ': Union g1 ('(m, b) ': g2)) ~ (Mul (Union g1 ('(m, b) ': g2)) :** a)
  )
  => MergeBy GT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE mergeBy #-}
  mergeBy =
    withCtxOb @('(m, b) ': g2)
      ( withSynOb @a
          ( ctxCase @g1
              (swap @k @(Interp (Mul ('(m, b) ': g2))) @(Interp a))
              ( associatorInv' (ctxOb @g1) (synOb @a) (ctxOb @('(m, b) ': g2))
                  . (ctxOb @g1 M.** swap @k @(Interp (Mul ('(m, b) ': g2))) @(Interp a))
                  . associator' (ctxOb @g1) (ctxOb @('(m, b) ': g2)) (synOb @a)
                  . (merge @g1 @('(m, b) ': g2) M.** synOb @a)
              )
          )
      )

instance
  ( Monoidal k
  , Merge ('(n, a) ': g1) g2
  , KnownObj a
  , KnownObj (b :: SYN k)
  , Mul ('(m, b) ': Union ('(n, a) ': g1) g2) ~ (Mul (Union ('(n, a) ': g1) g2) :** b)
  )
  => MergeBy LT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE mergeBy #-}
  mergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( associator' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
          . (merge @('(n, a) ': g1) @g2 M.** synOb @b)
      )

-- | A variable both contexts have is copied, one copy for each side.
instance
  ( SymMonoidal k
  , CocommutativeComonoid (Interp a)
  , KnownObj (a :: SYN k)
  , a ~ b
  , Merge g1 g2
  , KnownCtx (Union g1 g2)
  )
  => MergeBy EQ ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE mergeBy #-}
  mergeBy = ctxCase @g1 (ctxCase @g2 (comult @(Interp a)) withRest) withRest
    where
      -- When the variable is all both sides have, this is just the copy.
      withRest :: Interp (Mul ('(n, a) ': Union g1 g2)) ~> Interp (Mul ('(n, a) ': g1)) ** Interp (Mul ('(m, b) ': g2))
      withRest =
        withCtxOb @g1
          ( withCtxOb @g2
              ( withSynOb @a
                  ( (snoc @n @a @g1 M.** snoc @m @a @g2)
                      . swapInner @(Interp (Mul g1)) @(Interp (Mul g2)) @(Interp a) @(Interp a)
                      . (merge @g1 @g2 M.** comult @(Interp a))
                      . unsnoc @n @a @(Union g1 g2)
                  )
              )
          )

-- | The inverse of 'merge' for two contexts without a variable in common, which a @rec@ block
-- uses to put the wires it feeds back together with the others.
type Unmerge :: forall {k}. Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => Unmerge (g1 :: Ctx k) g2 where
  unmerge :: Interp (Mul g1) ** Interp (Mul g2) ~> Interp (Mul (Union g1 g2))

instance (Monoidal k, KnownCtx g2) => Unmerge ('[] :: Ctx k) g2 where
  {-# INLINE unmerge #-}
  unmerge = withCtxOb @g2 leftUnitor

instance (Monoidal k, KnownCtx ('(n, a) ': g1)) => Unmerge ('(n, a) ': g1 :: Ctx k) '[] where
  {-# INLINE unmerge #-}
  unmerge = withCtxOb @('(n, a) ': g1) rightUnitor

instance
  ( Monoidal k
  , KnownObj a
  , KnownObj b
  , KnownCtx g1
  , KnownCtx g2
  , UnmergeBy (CmpNat n m) ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  )
  => Unmerge ('(n, a) ': g1 :: Ctx k) ('(m, b) ': g2)
  where
  {-# INLINE unmerge #-}
  unmerge = unmergeBy @(CmpNat n m) @('(n, a) ': g1) @('(m, b) ': g2)

-- | 'unmerge' for two non-empty contexts, by which of the two has the larger head id.
type UnmergeBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Constraint
class (KnownCtx g1, KnownCtx g2) => UnmergeBy o (g1 :: Ctx k) g2 where
  unmergeBy :: Interp (Mul g1) ** Interp (Mul g2) ~> Interp (Mul (UnionBy o g1 g2))

instance
  ( SymMonoidal k
  , Unmerge g1 ('(m, b) ': g2)
  , KnownObj (a :: SYN k)
  , KnownObj b
  , Mul ('(n, a) ': Union g1 ('(m, b) ': g2)) ~ (Mul (Union g1 ('(m, b) ': g2)) :** a)
  )
  => UnmergeBy GT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE unmergeBy #-}
  unmergeBy =
    withCtxOb @('(m, b) ': g2)
      ( withSynOb @a
          ( ctxCase @g1
              (swap @k @(Interp a) @(Interp (Mul ('(m, b) ': g2))))
              ( (unmerge @g1 @('(m, b) ': g2) M.** synOb @a)
                  . associatorInv' (ctxOb @g1) (ctxOb @('(m, b) ': g2)) (synOb @a)
                  . (ctxOb @g1 M.** swap @k @(Interp a) @(Interp (Mul ('(m, b) ': g2))))
                  . associator' (ctxOb @g1) (synOb @a) (ctxOb @('(m, b) ': g2))
              )
          )
      )

instance
  ( Monoidal k
  , Unmerge ('(n, a) ': g1) g2
  , KnownObj a
  , KnownObj (b :: SYN k)
  , Mul ('(m, b) ': Union ('(n, a) ': g1) g2) ~ (Mul (Union ('(n, a) ': g1) g2) :** b)
  )
  => UnmergeBy LT ('(n, a) ': g1) ('(m, b) ': g2)
  where
  {-# INLINE unmergeBy #-}
  unmergeBy =
    ctxCase @g2
      (ctxOb @('(m, b) ': '(n, a) ': g1))
      ( (unmerge @('(n, a) ': g1) @g2 M.** synOb @b)
          . associatorInv' (ctxOb @('(n, a) ': g1)) (ctxOb @g2) (synOb @b)
      )

-- | Keep the variables of @g@ that @h@ has and discard the others, for an alternative of the
-- additives that does not use all the variables of the other. Every variable of @h@ must be in
-- @g@.
type Thin :: forall {k}. Ctx k -> Ctx k -> Constraint
class (KnownCtx g, KnownCtx h) => Thin (g :: Ctx k) h where
  thin :: Interp (Mul g) ~> Interp (Mul h)

instance (Monoidal k) => Thin ('[] :: Ctx k) '[] where
  {-# INLINE thin #-}
  thin = obj @(Unit :: k)

instance (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k), Thin g '[]) => Thin ('(n, a) ': g) '[] where
  {-# INLINE thin #-}
  thin = leftUnitor @k @Unit . (thin @g @'[] M.** counit @(Interp a)) . unsnoc @n @a @g

instance
  (KnownObj a, KnownObj b, KnownCtx g, KnownCtx h, ThinBy (CmpNat n m) ('(n, a) ': g) ('(m, b) ': h))
  => Thin ('(n, a) ': g :: Ctx k) ('(m, b) ': h)
  where
  {-# INLINE thin #-}
  thin = thinBy @(CmpNat n m) @('(n, a) ': g) @('(m, b) ': h)

-- | 'thin' for two non-empty contexts, by which of the two has the larger head id.
type ThinBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Constraint
class (KnownCtx g, KnownCtx h) => ThinBy o (g :: Ctx k) h where
  thinBy :: Interp (Mul g) ~> Interp (Mul h)

instance (Monoidal k, KnownObj (a :: SYN k), a ~ b, Thin g h) => ThinBy EQ ('(n, a) ': g) ('(m, b) ': h) where
  {-# INLINE thinBy #-}
  thinBy = withSynOb @a (snoc @m @a @h . (thin @g @h M.** synOb @a) . unsnoc @n @a @g)

instance
  (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k), KnownObj b, Thin g ('(m, b) ': h))
  => ThinBy GT ('(n, a) ': g) ('(m, b) ': h)
  where
  {-# INLINE thinBy #-}
  thinBy =
    withCtxOb @('(m, b) ': h)
      (rightUnitor . (thin @g @('(m, b) ': h) M.** counit @(Interp a)) . unsnoc @n @a @g)

-- | A binder's variable @n@ on the right of @r@, what the body uses besides it, given the body's
-- context @g@: 'snoc' if the body uses the variable, and its counit otherwise. The binder's
-- variable is the newest in scope, so it can only be at the head of @g@. The functional
-- dependency, rather than a type family, gives @r@, so that a binder costs one comparison of ids.
type BindVar :: forall {k}. Nat -> SYN k -> Ctx k -> Ctx k -> Constraint
class (KnownCtx r) => BindVar n (a :: SYN k) g r | n g -> r where
  bindVar :: Interp (Mul r) ** Interp a ~> Interp (Mul g)

instance (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k)) => BindVar n a '[] '[] where
  {-# INLINE bindVar #-}
  bindVar = rightUnitorWith @Unit (counit @(Interp a))

instance (KnownCtx r, BindVarBy (CmpNat n m) n a ('(m, b) ': g) r) => BindVar n (a :: SYN k) ('(m, b) ': g) r where
  {-# INLINE bindVar #-}
  bindVar = bindVarBy @(CmpNat n m) @n @a @('(m, b) ': g) @r

-- | 'bindVar' for a non-empty context, by whether its head is the new variable.
type BindVarBy :: forall {k}. Ordering -> Nat -> SYN k -> Ctx k -> Ctx k -> Constraint
class BindVarBy o n (a :: SYN k) g r | o n g -> r where
  bindVarBy :: Interp (Mul r) ** Interp a ~> Interp (Mul g)

instance (Monoidal k, KnownObj (a :: SYN k), a ~ b, KnownCtx g) => BindVarBy EQ n a ('(m, b) ': g) g where
  {-# INLINE bindVarBy #-}
  bindVarBy = snoc @m @a @g

instance
  (Monoidal k, Comonoid (Interp a), KnownObj (a :: SYN k), KnownObj b, KnownCtx g)
  => BindVarBy GT n a ('(m, b) ': g) ('(m, b) ': g)
  where
  {-# INLINE bindVarBy #-}
  bindVarBy =
    withCtxOb @('(m, b) ': g)
      (rightUnitorWith @(Interp (Mul ('(m, b) ': g))) (counit @(Interp a)))

type HeadId :: forall {k}. Ctx k -> Nat
type family HeadId g where
  HeadId ('(n, a) ': g) = n

-- | The variables of @g@ whose ids are not in @h@.
type Minus :: forall {k}. Ctx k -> Ctx k -> Ctx k
type family Minus g h where
  Minus '[] h = '[]
  Minus g '[] = g
  Minus ('(n, a) ': g) ('(m, b) ': h) = MinusBy (CmpNat n m) ('(n, a) ': g) ('(m, b) ': h)

type MinusBy :: forall {k}. Ordering -> Ctx k -> Ctx k -> Ctx k
type family MinusBy o g h where
  MinusBy GT (x ': g) h = x ': Minus g h
  MinusBy EQ (x ': g) (y ': h) = Minus g h
  MinusBy LT g (y ': h) = Minus g h

-- | The variables of @g@ whose ids are in @h@.
type Inter :: forall {k}. Ctx k -> Ctx k -> Ctx k
type Inter g h = Minus g (Minus g h)
