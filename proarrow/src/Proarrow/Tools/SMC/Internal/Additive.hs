{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": the additives. It exports everything, also what the
-- public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Additive where

import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (Promonad (..), obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))

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
  :: forall {k} (a :: SYN k) b d g. (HasBinaryProducts k, KnownObj a, KnownObj b) => Term d g (a :&& b) -> Term d g a
exl = lift @(a :&& b) @a (withSynOb @a (withSynOb @b (fst @k @(Interp a) @(Interp b))))

-- | The second alternative of a product.
{-# INLINE exr #-}
exr
  :: forall {k} (a :: SYN k) b d g. (HasBinaryProducts k, KnownObj a, KnownObj b) => Term d g (a :&& b) -> Term d g b
exr = lift @(a :&& b) @b (withSynOb @a (withSynOb @b (snd @k @(Interp a) @(Interp b))))

-- | Use up a term into the unit of the product.
{-# INLINE absorb #-}
absorb :: forall {k} (s :: SYN k) d g. (HasTerminalObject k, KnownObj s) => Term d g s -> Term d g Top
absorb = lift @s @Top (withSynOb @s (terminate @k @(Interp s)))

-- | The left injection into a coproduct.
{-# INLINE inl #-}
inl
  :: forall {k} (a :: SYN k) b d g
   . (HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => Term d g a -> Term d g (a :|| b)
inl = lift @a @(a :|| b) (withSynOb @a (withSynOb @b (lft @k @(Interp a) @(Interp b))))

-- | The right injection into a coproduct.
{-# INLINE inr #-}
inr
  :: forall {k} (a :: SYN k) b d g
   . (HasBinaryCoproducts k, KnownObj a, KnownObj b)
  => Term d g b -> Term d g (a :|| b)
inr = lift @b @(a :|| b) (withSynOb @a (withSynOb @b (rgt @k @(Interp a) @(Interp b))))

-- | Case analysis on a coproduct. Each branch receives the contents of its alternative through a
-- pattern (see /Patterns/), and the variables of the term around it are shared between the
-- branches. This needs the tensor to distribute over the coproduct.
{-# INLINE caseOf #-}
caseOf
  :: forall {k} (a :: SYN k) b c d g r1 r2 t1 cont1 t2 cont2
   . ( Distributive k
     , KnownObj a
     , KnownObj b
     , Binds d r1 a c t1 cont1
     , Binds d r2 b c t2 cont2
     , Thin (Union r1 r2) r1
     , Thin (Union r1 r2) r2
     , Merge (Union r1 r2) g
     )
  => Term d g (a :|| b)
  -> (t1 -> cont1)
  -> (t2 -> cont2)
  -> Term d (Union (Union r1 r2) g) c
caseOf (MkTerm x) f h =
  withCtxOb @(Union r1 r2)
    ( withSynOb @a
        ( withSynOb @b
            ( MkTerm
                ( ( (bound @d @r1 @a @c f . (thin @(Union r1 r2) @r1 M.** obj @(Interp a)))
                      ||| (bound @d @r2 @b @c h . (thin @(Union r1 r2) @r2 M.** obj @(Interp b)))
                  )
                    . distL @k @(Interp (Mul (Union r1 r2))) @(Interp a) @(Interp b)
                    . (ctxOb @(Union r1 r2) M.** x)
                    . merge @(Union r1 r2) @g
                )
            )
        )
    )

-- | There is no term of 'Zero', so from one, together with the rest of the context, anything
-- follows.
{-# INLINE absurd #-}
absurd
  :: forall {k} (s :: SYN k) c d g1 g2
   . (Distributive k, KnownObj s, KnownObj c, Merge g1 g2)
  => Term d g1 s -> Term d g2 Zero -> Term d (Union g1 g2) c
absurd e z = lift @(s :** Zero) @c (withSynOb @s (withSynOb @c (initiate @k @(Interp c) . absorbL @k @(Interp s)))) (e ** z)
