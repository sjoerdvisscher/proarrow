{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Internal module of "Proarrow.Tools.SMC": the type expressions of terms, and how they stand for
-- objects. It exports everything, also what the public module keeps hidden.
module Proarrow.Tools.SMC.Internal.Syntax where

import Data.Kind (Constraint)
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CategoryOf (..), obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (Obj)

infixl 7 :**
infixl 6 :&&
infixl 6 :||
infixr 5 :->

-- | Type expressions over the objects of @k@: an object of @k@, the unit, the tensor, the
-- internal hom and the negation, and the additives: the product and its unit 'Top', and the
-- coproduct and its unit 'Zero'.
--
-- The negation gives the types a polarity: a type is negative when it is a 'Not', and positive
-- otherwise. A term of a positive type is a value, and a term of a negative type is a consumer
-- of what it negates. 'Proarrow.Tools.SMC.Up' shifts a positive type to a negative one, and 'Dn' a negative type to
-- a positive one, standing for the same object: a term of @'Dn' n@ is a stored term of @n@.
type data SYN k
  = F k
  | I
  | SYN k :** SYN k
  | SYN k :-> SYN k
  | Not (SYN k)
  | Dn (SYN k)
  | SYN k :&& SYN k
  | Top
  | SYN k :|| SYN k
  | Zero

-- | The object of @k@ a type expression stands for.
type Interp :: forall {k}. SYN k -> k
type family Interp s where
  Interp (F a) = a
  Interp I = Unit
  Interp (a :** b) = Interp a ** Interp b
  Interp (a :-> b) = Interp a ~~> Interp b
  Interp (Not a) = Dual (Interp a)
  Interp (Dn a) = Interp a
  Interp (a :&& b) = Interp a && Interp b
  Interp Top = TerminalObject
  Interp (a :|| b) = Interp a || Interp b
  Interp Zero = InitialObject

-- | Type expressions whose 'Interp' is an object, given that their leaves are.
type KnownObj :: forall {k}. SYN k -> Constraint
class (CategoryOf k) => KnownObj (s :: SYN k) where
  withSynOb :: ((Ob (Interp s)) => r) -> r

instance (CategoryOf k, Ob (a :: k)) => KnownObj (F a) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

instance (Monoidal k) => KnownObj (I :: SYN k) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

instance (Monoidal k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :** b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withOb2 @k @(Interp a) @(Interp b) r))

instance (Closed k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :-> b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withObExp @k @(Interp a) @(Interp b) r))

instance (KnownObj (a :: SYN k)) => KnownObj (Dn a) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a r

instance (Dialogue k, KnownObj (a :: SYN k)) => KnownObj (Not a) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withObDual @k @(Interp a) r)

instance (HasBinaryProducts k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :&& b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withObProd @k @(Interp a) @(Interp b) r))

instance (HasTerminalObject k) => KnownObj (Top :: SYN k) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

instance (HasBinaryCoproducts k, KnownObj a, KnownObj (b :: SYN k)) => KnownObj (a :|| b) where
  {-# INLINE withSynOb #-}
  withSynOb r = withSynOb @a (withSynOb @b (withObCoprod @k @(Interp a) @(Interp b) r))

instance (HasInitialObject k) => KnownObj (Zero :: SYN k) where
  {-# INLINE withSynOb #-}
  withSynOb r = r

-- | The identity on the object a type expression stands for.
{-# INLINE synOb #-}
synOb :: forall {k} (s :: SYN k). (KnownObj s) => Obj (Interp s)
synOb = withSynOb @s (obj @(Interp s))
