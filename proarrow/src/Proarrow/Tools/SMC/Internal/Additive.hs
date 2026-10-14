{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": the additives. It exports everything, also what the
-- public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Additive where

import Data.Kind (Constraint)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Distributive (Distributive (..), DistributiveProfunctor, branch)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, Profunctor (..), Promonad (..), obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (pattern Objs)
import Prelude (($), type (~))

import Proarrow.Tools.SMC.Internal.Context
import Proarrow.Tools.SMC.Internal.Pattern
import Proarrow.Tools.SMC.Internal.Syntax
import Proarrow.Tools.SMC.Internal.Term

-- | Both of two alternatives over the same variables: the product. This needs products.
{-# INLINE with #-}
with
  :: forall {k} (a :: SYN k) b d g1 g2
   . (HasBinaryProducts k, Thin (Union g1 g2) g1, Thin (Union g1 g2) g2)
  => Term d g1 a
  -> Term d g2 b
  -> Term d (Union g1 g2) (a :&& b)
with (MkTerm f) (MkTerm h) = MkTerm ((f . thin @(Union g1 g2) @g1) &&& (h . thin @(Union g1 g2) @g2))

-- | The first alternative of a product.
{-# INLINE exl #-}
exl
  :: forall {k} {p} (a :: SYN k) b d g
   . (HasBinaryProducts k, Profunctor p, KnownObj a, KnownObj b) => TermP p d g (a :&& b) -> TermP p d g a
exl = rmapT (withSynOb @a (withSynOb @b (fst @k @(Interp a) @(Interp b))))

-- | The second alternative of a product.
{-# INLINE exr #-}
exr
  :: forall {k} {p} (a :: SYN k) b d g
   . (HasBinaryProducts k, Profunctor p, KnownObj a, KnownObj b) => TermP p d g (a :&& b) -> TermP p d g b
exr = rmapT (withSynOb @a (withSynOb @b (snd @k @(Interp a) @(Interp b))))

-- | Use up a term into the unit of the product.
{-# INLINE absorb #-}
absorb
  :: forall {k} {p} (s :: SYN k) d g. (HasTerminalObject k, Profunctor p, KnownObj s) => TermP p d g s -> TermP p d g Top
absorb = rmapT (withSynOb @s (terminate @k @(Interp s)))

-- | The left injection into a coproduct.
{-# INLINE inl #-}
inl
  :: forall {k} (a :: SYN k) b d g p
   . (Profunctor p, HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => TermP p d g a -> TermP p d g (a :|| b)
inl = rmapT @a @(a :|| b) (withSynOb @a (withSynOb @b (lft @k @(Interp a) @(Interp b))))

-- | The right injection into a coproduct.
{-# INLINE inr #-}
inr
  :: forall {k} (a :: SYN k) b d g p
   . (Profunctor p, HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => TermP p d g b -> TermP p d g (a :|| b)
inr = rmapT @b @(a :|| b) (withSynOb @a (withSynOb @b (rgt @k @(Interp a) @(Interp b))))

-- | A sum with components @a@ and @b@: either @a ':||' b@ or a coproduct embedded by 'F'.
type Sum :: forall {k}. SYN k -> SYN k -> SYN k -> Constraint
class (Interp s ~ Interp (a :|| b)) => Sum s a b

-- An unknown input defaults to syntax-level choice, as patterns default to syntax-level tensor.
-- The embedded instance takes over when the input is known to be headed by F.
instance {-# INCOHERENT #-} (s ~ (a :|| b)) => Sum s a b

instance (z ~ (x || y), a ~ F x, b ~ F y) => Sum (F z) a b

-- | Case analysis on a coproduct. Each branch receives the contents of its alternative through a
-- pattern (see /Patterns/), and the variables of the term around it are shared between the
-- branches. This needs the tensor to distribute over the coproduct.
-- The sum may be written with '(:||)' or embedded by 'F', as in the result of '(-<)'.
-- For 'Proarrow.Profunctor.Instance.Arrow.Arr', this needs 'Control.Arrow.ArrowChoice'
-- and runs only the selected branch.
{-# INLINE caseOf #-}
caseOf
  :: forall {k} (a :: SYN k) b c d g r1 r2 t1 cont1 t2 cont2 s (p :: CAT k)
   . ( Distributive k
     , Promonad p
     , DistributiveProfunctor p
     , Sum s a b
     , KnownObj a
     , KnownObj b
     , Binds p d r1 a c t1 cont1
     , Binds p d r2 b c t2 cont2
     , Thin (Union r1 r2) r1
     , Thin (Union r1 r2) r2
     , Merge (Union r1 r2) g
     )
  => TermP p d g s
  -> (t1 -> cont1)
  -> (t2 -> cont2)
  -> TermP p d (Union (Union r1 r2) g) c
caseOf (MkTerm x) f h =
  withCtxOb @(Union r1 r2)
    ( withSynOb @a
        ( withSynOb @b
            ( case lmap (thin @(Union r1 r2) @r1 M.** obj @(Interp a)) (bound @p @d @r1 @a @c f) of
                l@Objs -> case lmap (thin @(Union r1 r2) @r2 M.** obj @(Interp b)) (bound @p @d @r2 @b @c h) of
                  r@Objs ->
                    MkTerm $
                      lmap (merge @(Union r1 r2) @g) $
                        branch
                          (rmap (distL @k @(Interp (Mul (Union r1 r2))) @(Interp a) @(Interp b)) (id @p @(Interp (Mul (Union r1 r2))) M.** x))
                          l
                          r
            )
        )
    )

-- | There is no term of 'Zero', so from one, together with the rest of the context, anything
-- follows.
{-# INLINE absurd #-}
absurd
  :: forall {k} {p} (s :: SYN k) c d g1 g2
   . (Distributive k, M.MonoidalProfunctor p, KnownObj s, KnownObj c, Merge g1 g2)
  => TermP p d g1 s -> TermP p d g2 Zero -> TermP p d (Union g1 g2) c
absurd e z = rmapT (withSynOb @s (withSynOb @c (initiate @k @(Interp c) . absorbL @k @(Interp s)))) (e ** z)
