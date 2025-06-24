{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Helper.CCC
  ( toCCC
  , lam
  , ($)
  , lift
  , pattern (:&)
  , Free (Lft, Rgt)
  , either
  , InitF
  , TermF
  , type (*!)
  , type (+)
  , type (-->)
  , FK (..)
  ) where

import Data.Kind (Constraint, Type)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Monoidal.Distributive (distLProd)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN)
import Proarrow.Object (Obj, obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft', rgt')
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..), fst', snd')
import Proarrow.Object.Exponential (BiCCC, Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate')

type Cast :: forall {k}. [FK k] -> [FK k] -> Constraint
class Cast i j where
  cast :: (IsFK a) => Free j a -> Free i a

instance {-# OVERLAPPABLE #-} (Cast i j, (a ': i) ~ i', IsFK a, IsFKs i) => Cast i' j where
  cast = Tail . cast @i @j

instance Cast i i where
  cast f = f

pattern Uncurry :: (IsFK (a :: FK k), IsFK (b :: FK k), IsFKs (i :: [FK k]), Closed k) => Free i (a --> b) -> Free (a : i) b
pattern Uncurry f = Apply (Tail f) Head

lam
  :: forall {k} a b i
   . (IsFK a, IsFK b, IsFKs i)
  => ((forall (x :: [FK k]). (Cast x (a ': i)) => Free x a) -> Free (a ': i) b)
  -> Free i (a --> b)
lam f = Curry (f xa)
  where
    xa :: forall (x :: [FK k]). (Cast x (a ': i)) => Free x a
    xa = cast @x @(a ': i) Head

infixr 0 $
($) :: (IsFK a, IsFK b, IsFKs i) => Free i (a --> b) -> Free i a -> Free i b
($) = Apply

lift :: a ~> b -> Free i (F a) -> Free i (F b)
lift = L

fstSnd :: (IsFK a, IsFK b, IsFKs i) => Free i (a *! b) -> (Free i a, Free i b)
fstSnd f = (Fst f, Snd f)

pattern (:&) :: (IsFK a, IsFK b, IsFKs i) => Free i a -> Free i b -> Free i (a *! b)
pattern x :& y <- (fstSnd -> (x, y))
  where
    x :& y = Prd x y

{-# COMPLETE (:&) #-}

either
  :: forall {k} (a :: FK k) b c i
   . (IsFK a, IsFK b, IsFK c, IsFKs i, Closed k)
  => Free i (a --> c)
  -> Free i (b --> c)
  -> Free i (a + b)
  -> Free i c
either f g m = Sum m (Uncurry f) (Uncurry g)

type MultiCat k = [k] -> k -> Type
data FK k = F k
type instance UN F (F a) = a

infixr 2 -->

data family InitF :: k
data family TermF :: k
data family (+) (a :: k) (b :: k) :: k
data family (*!) (a :: k) (b :: k) :: k
data family (-->) (a :: k) (b :: k) :: k

type family Mul as where
  Mul '[] = TermF
  Mul '[a] = a
  Mul (a ': as) = Mul as *! a

data Free :: MultiCat (FK k) where
  Id :: (IsFK a) => Free '[a] a
  L :: a ~> b -> Free i (F a) -> Free i (F b)
  Head :: (IsFK a, IsFKs i) => Free (a ': i) a
  Tail :: (IsFK a, IsFK b, IsFKs i) => Free i b -> Free (a ': i) b
  Ini :: (IsFK a, IsFKs i) => Free i InitF -> Free i a
  Ter :: (IsFKs i) => Free i TermF
  Fst :: (IsFK a, IsFK b, IsFKs i) => Free i (a *! b) -> Free i a
  Snd :: (IsFK a, IsFK b, IsFKs i) => Free i (a *! b) -> Free i b
  Prd :: (IsFK a, IsFK b, IsFKs i) => Free i a -> Free i b -> Free i (a *! b)
  Lft :: (IsFK a, IsFK b, IsFKs i) => Free i a -> Free i (a + b)
  Rgt :: (IsFK a, IsFK b, IsFKs i) => Free i b -> Free i (a + b)
  Sum :: (IsFK a, IsFK b, IsFK c, IsFKs i) => Free i (a + b) -> Free (a ': i) c -> Free (b ': i) c -> Free i c
  Curry :: (IsFK a, IsFK b, IsFKs i) => Free (a ': i) b -> Free i (a --> b)
  Apply :: (IsFK a, IsFK b, IsFKs i) => Free i (a --> b) -> Free i a -> Free i b

instance P.Show (Free a b) where
  show Id = "fst"
  show (L _ Id) = "<arrow>"
  show (L _ f) = "(<arrow> . " P.++ P.show f P.++ ")"
  show Head = "snd"
  show (Tail f) = "(" P.++ P.show f P.++ " . fst)"
  show (Ini f) = "(initiate . " P.++ P.show f P.++ ")"
  show Ter = "terminate"
  show (Lft Id) = "lft"
  show (Lft f) = "(lft . " P.++ P.show f P.++ ")"
  show (Rgt Id) = "rgt"
  show (Rgt f) = "(rgt . " P.++ P.show f P.++ ")"
  show (Sum Id f g) = "(" P.++ P.show f P.++ " ||| " P.++ P.show g P.++ ")"
  show (Sum m f g) = "((" P.++ P.show f P.++ " ||| " P.++ P.show g P.++ ") . " P.++ P.show m P.++ ")"
  show (Fst Id) = "fst"
  show (Fst f) = "(fst . " P.++ P.show f P.++ ")"
  show (Snd Id) = "snd"
  show (Snd f) = "(snd . " P.++ P.show f P.++ ")"
  show (Prd f g) = "(" P.++ P.show f P.++ " &&& " P.++ P.show g P.++ ")"
  show (Curry f) = "(curry " P.++ P.show f P.++ ")"
  show (Apply f a) = "(" P.++ P.show f P.++ " $ " P.++ P.show a P.++ ")"

type family FromFree (t :: FK k) :: k
type instance FromFree (F a) = a
type instance FromFree InitF = InitialObject
type instance FromFree TermF = TerminalObject
type instance FromFree (a + b) = FromFree a || FromFree b
type instance FromFree (a *! b) = FromFree a && FromFree b
type instance FromFree (a --> b) = FromFree a ~~> FromFree b

type IsFKs :: forall {k}. [FK k] -> Constraint
class (Cartesian k) => IsFKs (i :: [FK k]) where
  head :: (IsFK b) => FromFree (Mul (b : i)) ~> FromFree b
  tail :: (IsFK b) => FromFree (Mul (b : i)) ~> FromFree (Mul i)
  snoc :: (IsFK b) => FromFree (Mul i) && FromFree b ~> FromFree (Mul (b : i))
  fromFreeObjs :: Obj (FromFree (Mul i))
  fromFreeObjs1 :: (IsFK b) => Obj (FromFree (Mul (b : i)))
instance (Cartesian k) => IsFKs ('[] :: [FK k]) where
  head @b = fromFreeObj @b
  tail @b = terminate \\ fromFreeObj @b
  snoc @b = snd @_ @TerminalObject \\ fromFreeObj @b
  fromFreeObjs = id
  fromFreeObjs1 @b = fromFreeObj @b
instance (IsFKs i, IsFK (a :: FK k)) => IsFKs (a : i) where
  head @b = snd' (fromFreeObjs1 @i @a) (fromFreeObj @b)
  tail @b = fst' (fromFreeObjs1 @i @a) (fromFreeObj @b)
  snoc @b = fromFreeObjs1 @i @a *** fromFreeObj @b
  fromFreeObjs = fromFreeObjs1 @i @a
  fromFreeObjs1 @b = fromFreeObjs1 @i @a *** fromFreeObj @b

fromFree :: (BiCCC k) => Free (i :: [FK k]) a -> FromFree (Mul i) ~> FromFree a
fromFree (Id @a) = head @'[] @a
fromFree (L f g) = f . fromFree g
fromFree (Head @a @i) = head @i @a
fromFree (Tail @a @_ @i f) = fromFree f . tail @i @a
fromFree (Ini @a f) = initiate @_ @(FromFree a) . fromFree f \\ fromFreeObj @a
fromFree (Ter @i) = terminate' (fromFreeObjs @i)
fromFree (Lft @a @b f) = lft' (fromFreeObj @a) (fromFreeObj @b) . fromFree f
fromFree (Rgt @a @b f) = rgt' (fromFreeObj @a) (fromFreeObj @b) . fromFree f
fromFree (Sum @a @b @_ @i m f g) =
  let ff = fromFree f; fg = fromFree g; fi = fromFreeObjs @i
  in ( (ff . snoc @i @a ||| fg . snoc @i @b) . distLProd @(FromFree (Mul i)) @(FromFree a) @(FromFree b) . (fi &&& fromFree m)
     )
      \\ fi
      \\ fromFreeObj @a
      \\ fromFreeObj @b
fromFree (Fst @a @b f) = fst' (fromFreeObj @a) (fromFreeObj @b) . fromFree f
fromFree (Snd @a @b f) = snd' (fromFreeObj @a) (fromFreeObj @b) . fromFree f
fromFree (Prd f g) = fromFree f &&& fromFree g
fromFree (Curry @a @b @i f) =
  curry @_ @(FromFree (Mul i)) @(FromFree a) @(FromFree b) (fromFree f . snoc @i @a) \\ fromFreeObj @a \\ fromFreeObjs @i
fromFree (Apply @a @b f g) = apply @_ @(FromFree a) @(FromFree b) . (fromFree f &&& fromFree g) \\ fromFreeObj @a \\ fromFreeObj @b

type IsFK :: forall {k}. FK k -> Constraint
class IsFK (a :: FK k) where
  fromFreeObj :: Obj (FromFree a)
instance (CategoryOf k, Ob a) => IsFK (F (a :: k)) where
  fromFreeObj = id
instance (HasInitialObject k) => IsFK (InitF :: FK k) where
  fromFreeObj = obj
instance (HasTerminalObject k) => IsFK (TermF :: FK k) where
  fromFreeObj = obj
instance (HasBinaryCoproducts k, IsFK a, IsFK b) => IsFK (a + b :: FK k) where
  fromFreeObj = fromFreeObj @a +++ fromFreeObj @b
instance (HasBinaryProducts k, IsFK a, IsFK b) => IsFK (a *! b :: FK k) where
  fromFreeObj = fromFreeObj @a *** fromFreeObj @b
instance (Closed k, IsFK a, IsFK b) => IsFK (a --> b :: FK k) where
  fromFreeObj = fromFreeObj @b ^^^ fromFreeObj @a

-- | Adapted from Phil Freeman: https://blog.functorial.com/posts/2017-10-08-HOAS-CCCs.html
toCCC :: forall {k} a b. (BiCCC k) => (IsFK (a :: FK k), IsFK b) => (Free '[] (a --> b)) -> FromFree a ~> FromFree b
toCCC f = fromFree (Uncurry f)

-- debug :: (IsFK a, IsFK b) => Free '[] ((a :: FK ()) --> b) -> P.String
-- debug f = P.show (Uncurry f)

-- test1 :: forall {k} (a :: k) b. (BiCCC k, Ob (a :: k), Ob b) => a ~> b || a
-- test1 = toCCC @(F a) @(F b + F a) (lam \x -> Rgt x)
-- test2 :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => a && b ~> b && a
-- test2 = toCCC @(F a *! F b) @(F b *! F a) (lam \(x :& y) -> (y :& x))
-- test3 :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => (a ~~> b) && a ~> b
-- test3 = toCCC @((F a --> F b) *! F a) @(F b) (lam \(f :& a) -> f $ a)
-- test4 :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => a ~> b ~~> (a && b)
-- test4 = toCCC @(F a) @(F b --> F a *! F b) (lam \x -> lam \y -> (x :& y))
-- test5 :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => (a && b) ~> (b && a)
-- test5 = toCCC @(F a *! F b) @(F b *! F a) (lam \(a :& b) -> lam (\c -> (b :& c)) $ a)
-- test6 :: forall {k} a b c. (BiCCC k, Ob (a :: k), Ob b, Ob c) => b ~~> a ~~> b ~~> c ~> a ~~> b ~~> c
-- test6 = toCCC @(F b --> F a --> F b --> F c) @(F a --> F b --> F c) (lam (\x -> lam (\y -> lam (\z -> ((x $ z) $ y) $ z))))
-- test7 :: forall {k} a b. (BiCCC k, Ob (a :: k), Ob b) => (a || b) ~> (b || a)
-- test7 = toCCC @(F a + F b) @(F b + F a) (lam \x -> either (lam \y -> Rgt y) (lam \y -> Lft y) x)
-- test8 :: forall {k} (a :: k) b c. (BiCCC k, Ob a, Ob b, Ob c) => a && (b || c) ~> (a && b) || (a && c)
-- test8 =
--   toCCC @(F a *! (F b + F c)) @((F a *! F b) + (F a *! F c))
--     (lam \(a :& bc) -> either (lam \b -> Lft (Tail a :& b)) (lam \c -> Rgt (Tail a :& c)) bc)
