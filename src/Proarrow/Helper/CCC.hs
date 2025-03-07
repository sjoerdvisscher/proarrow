{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Helper.CCC (toCCC, lam, ($), lift, pattern (:&), left, right, either, FreeCCC, InitF, TermF, type (*), type (+), type (-->), FK(..)) where

import Data.Kind (Constraint)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Object (Obj, obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), lft', rgt')
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , associatorProd
  , associatorProdInv
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  , fst'
  , snd'
  )
import Proarrow.Object.Exponential (BiCCC, CCC, Closed (..), eval, lower, curry', uncurry')
import Proarrow.Object.Initial (HasInitialObject (..), initiate')
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate')

class (CCC k) => Cast (x :: k) y where
  cast :: x ~> y

instance {-# OVERLAPPABLE #-} (CCC k, Cast b a, b && i ~ t, Ob b, Ob i) => Cast (t :: k) a where
  cast = cast . fst @k @b @i

instance (CCC k, Ob a) => Cast (a :: k) a where
  cast = id

lam
  :: forall {k} a b i
   . (CCC k, Ob i, Ob a, Ob b)
  => ((forall (x :: k). (Cast x (i && a)) => x ~> a) -> (i && a) ~> b)
  -> (i :: k) ~> (a ~~> b)
lam f = curry @k @i @a @b (f snd_)
  where
    snd_ :: forall x. (Cast x (i && a)) => x ~> a
    snd_ = snd @k @i @a . cast @k @x @(i && a)

($) :: forall {k} i a b. (CCC k, Ob b) => (i :: k) ~> (a ~~> b) -> i ~> a -> i ~> b
($) f a = eval @a @b . (f &&& a) \\ a

lift :: forall {k} (a :: FK k) b i. (BiCCC k, Ob a, Ob b) => FromFree a ~> FromFree b -> i ~> a -> i ~> b
lift f = lift' (L f)

lift' :: forall {k} (i :: k) a b. (CCC k) => a ~> b -> i ~> a -> i ~> b
lift' = (.)

fstSnd :: forall {k} (i :: k) a b. (CCC k, Ob a, Ob b) => i ~> a && b -> (i ~> a, i ~> b)
fstSnd f = (lift' (fst @k @a @b) f, lift' (snd @k @a @b) f)

pattern (:&) :: forall {k} i a b. (CCC k, Ob (a :: k), Ob b) => (i ~> a) -> (i ~> b) -> i ~> a && b
pattern x :& y <- (fstSnd @i @a @b -> (x, y))
  where
    x :& y = x &&& y

{-# COMPLETE (:&) #-}

left :: forall {k} a b i. (HasBinaryCoproducts k, Ob (a :: k), Ob b) => (i ~> a) -> i ~> a || b
left x = lft @_ @a @b . x

right :: forall {k} a b i. (HasBinaryCoproducts k, Ob (a :: k), Ob b) => (i ~> b) -> i ~> a || b
right x = rgt @_ @a @b . x

either
  :: forall {k} a b c i
   . (HasBinaryCoproducts k, CCC k, Ob (a :: k), Ob b, Ob c)
  => i ~> a ~~> c
  -> i ~> b ~~> c
  -> i ~> (a || b) ~~> c
either f g = swapExp @(a || b) @i @c (swapExp @i @a @c f ||| swapExp @i @b @c g) \\ f

swapExp :: forall {k} (a :: k) b c. (CCC k, Ob b, Ob c) => a ~> b ~~> c -> b ~> a ~~> c
swapExp f = curry @k @b @a @c (uncurry @k @b @c @a f . swapProd @b @a) \\ f

data FK k = F k
type instance UN F (F a) = a

infixr 2 -->

data family InitF :: k
data family TermF :: k
data family (+) (a :: k) (b :: k) :: k
data family (*) (a :: k) (b :: k) :: k
data family (-->) (a :: k) (b :: k) :: k

data FreeCCC :: CAT (FK k) where
  Id :: (Ob a) => FreeCCC a a
  Comp :: FreeCCC b c -> FreeCCC a b -> FreeCCC a c
  Ini :: (Ob a) => FreeCCC InitF a
  Ter :: (Ob a) => FreeCCC a TermF
  Lft :: (Ob a, Ob b) => FreeCCC a (a + b)
  Rgt :: (Ob a, Ob b) => FreeCCC b (a + b)
  Sum :: FreeCCC a c -> FreeCCC b c -> FreeCCC (a + b) c
  Fst :: (Ob a, Ob b) => FreeCCC (a * b) a
  Snd :: (Ob a, Ob b) => FreeCCC (a * b) b
  Prd :: FreeCCC a b -> FreeCCC a c -> FreeCCC a (b * c)
  Curry :: (Ob a, Ob b) => FreeCCC (a * b) c -> FreeCCC a (b --> c)
  Uncurry :: (Ob b, Ob c) => FreeCCC a (b --> c) -> FreeCCC (a * b) c
  Ex :: FreeCCC b y -> FreeCCC x a -> FreeCCC (a --> b) (x --> y)
  L :: (Ob a, Ob b) => FromFree a ~> FromFree b -> FreeCCC a b

instance P.Show (FreeCCC a b) where
  show Id = "id"
  show (Comp f g) = "(" P.++ P.show f P.++ " . " P.++ P.show g P.++ ")"
  show Ini = "initiate"
  show Ter = "terminate"
  show Lft = "lft"
  show Rgt = "rgt"
  show (Sum f g) = "(" P.++ P.show f P.++ " ||| " P.++ P.show g P.++ ")"
  show Fst = "fst"
  show Snd = "snd"
  show (Prd f g) = "(" P.++ P.show f P.++ " &&& " P.++ P.show g P.++ ")"
  show (Curry f) = "(" P.++ "curry " P.++ P.show f P.++ ")"
  show (Uncurry f) = "(" P.++ "uncurry " P.++ P.show f P.++ ")"
  show (Ex f g) = "(" P.++ "ex " P.++ P.show f P.++ " " P.++ P.show g P.++ ")"
  show (L _) = "<arrow>"

type family FromFree (t :: FK k) :: k where
  FromFree (F a) = a
  FromFree InitF = InitialObject
  FromFree TermF = TerminalObject
  FromFree (a + b) = FromFree a || FromFree b
  FromFree (a * b) = FromFree a && FromFree b
  FromFree (a --> b) = FromFree a ~~> FromFree b

type IsFK :: forall {k}. FK k -> Constraint
class IsFK (a :: FK k) where
  fkId :: a ~> a
  fromFreeObj :: Obj (FromFree a)
instance (CategoryOf k, Ob a) => IsFK (F (a :: k)) where
  fkId = Id
  fromFreeObj = id
instance (HasInitialObject k) => IsFK (InitF :: FK k) where
  fkId = Ini
  fromFreeObj = obj
instance (HasTerminalObject k) => IsFK (TermF :: FK k) where
  fkId = Ter
  fromFreeObj = obj
instance (HasBinaryCoproducts k, IsFK a, IsFK b) => IsFK (a + b :: FK k) where
  fkId = Sum Lft Rgt
  fromFreeObj = fromFreeObj @a +++ fromFreeObj @b
instance (HasBinaryProducts k, IsFK a, IsFK b) => IsFK (a * b :: FK k) where
  fkId = Prd Fst Snd
  fromFreeObj = fromFreeObj @a *** fromFreeObj @b
instance (Closed k, IsFK a, IsFK b) => IsFK (a --> b :: FK k) where
  fkId = Ex fkId fkId
  fromFreeObj = fromFreeObj @b ^^^ fromFreeObj @a
instance (BiCCC k) => Profunctor (FreeCCC :: CAT (FK k)) where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Comp f g = r \\ f \\ g
  r \\ Ini = r
  r \\ Ter = r
  r \\ Lft = r
  r \\ Rgt = r
  r \\ Sum f g = r \\ f \\ g
  r \\ Fst = r
  r \\ Snd = r
  r \\ Prd f g = r \\ f \\ g
  r \\ Curry f = r \\ f
  r \\ Uncurry f = r \\ f
  r \\ Ex f g = r \\ f \\ g
  r \\ L f = r \\ f
instance (BiCCC k) => Promonad (FreeCCC :: CAT (FK k)) where
  id = fkId
  Id . r = r
  Comp l1 l2 . r = l1 . (l2 . r)
  l . Id = l
  l . r = case r of
    Comp r1 r2 -> case simplify l r1 of
      Comp a b -> Comp a (Comp b r2)
      a -> Comp a r2
    _ -> simplify l r
    where
      simplify :: (BiCCC k) => FreeCCC (b :: FK k) c -> FreeCCC a b -> FreeCCC a c
      simplify Fst (Prd f _) = f
      simplify Snd (Prd _ g) = g
      simplify Ter g = Ter \\ g
      simplify f Ini = Ini \\ f
      simplify (Ex f g) (Ex h i) = Ex (f . h) (i . g)
      simplify (Prd f g) h = Prd (f . h) (g . h)
      simplify f (Sum g h) = Sum (f . g) (f . h)
      simplify f g = Comp f g
instance (BiCCC k) => CategoryOf (FK k) where
  type (~>) = FreeCCC
  type Ob (a :: FK k) = IsFK a
instance (BiCCC k) => HasInitialObject (FK k) where
  type InitialObject = InitF
  initiate = Ini
instance (BiCCC k) => HasTerminalObject (FK k) where
  type TerminalObject = TermF
  terminate = Ter
instance (BiCCC k) => HasBinaryCoproducts (FK k) where
  type a || b = a + b
  withObCoprod r = r
  lft = Lft
  rgt = Rgt
  Lft ||| Rgt = Id
  l ||| r = Sum l r
instance (BiCCC k) => HasBinaryProducts (FK k) where
  type a && b = a * b
  withObProd r = r
  fst = Fst
  snd = Snd
  Fst &&& Snd = Id
  l &&& r = Prd l r
instance (BiCCC k) => MonoidalProfunctor (FreeCCC :: CAT (FK k)) where
  par0 = id
  par = (***)
instance (BiCCC k) => Monoidal (FK k) where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 r = r
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv
instance (BiCCC k) => SymMonoidal (FK k) where
  swap = swapProd
instance (BiCCC k) => Closed (FK k) where
  type a ~~> b = a --> b
  withObExp r = r
  curry (Uncurry f) = f
  curry (Comp f (Uncurry g)) = (f ^^^ id) . g
  curry f = Curry f
  uncurry (Curry f) = f
  uncurry (Comp (Curry f) g) = f . (g *** Id)
  uncurry f = Uncurry f
  Id ^^^ Id = Id
  l ^^^ r = Ex l r

fromFree :: (BiCCC k, Ob a, Ob b) => FreeCCC (a :: FK k) b -> FromFree a ~> FromFree b
fromFree (Id @a) = fromFreeObj @a
fromFree (Comp f g) = fromFree f . fromFree g \\ f
fromFree (Ini @a) = initiate' (fromFreeObj @a)
fromFree (Ter @a) = terminate' (fromFreeObj @a)
fromFree (Lft @a @b) = lft' (fromFreeObj @a) (fromFreeObj @b)
fromFree (Rgt @a @b) = rgt' (fromFreeObj @a) (fromFreeObj @b)
fromFree (Sum f g) = (fromFree f ||| fromFree g) \\ f \\ g
fromFree (Fst @a @b) = fst' (fromFreeObj @a) (fromFreeObj @b)
fromFree (Snd @a @b) = snd' (fromFreeObj @a) (fromFreeObj @b)
fromFree (Prd f g) = (fromFree f &&& fromFree g) \\ f \\ g
fromFree (Curry @a @b f) = curry' (fromFreeObj @a) (fromFreeObj @b) (fromFree f) \\ f
fromFree (Uncurry @b @c f) = uncurry' (fromFreeObj @b) (fromFreeObj @c) (fromFree f) \\ f
fromFree (Ex f g) = fromFree f ^^^ fromFree g \\ f \\ g
fromFree (L f) = f

-- | Adapted from Phil Freeman: https://blog.functorial.com/posts/2017-10-08-HOAS-CCCs.html
toCCC :: forall {k} a b. (BiCCC k) => (Ob (a :: FK k), Ob b) => (TermF ~> (a --> b)) -> FromFree a ~> FromFree b
toCCC = fromFree . lower

-- debug :: (a :: FK ()) ~> b -> P.String
-- debug = P.show

-- test1 :: forall {k} (a :: k) b. (BiCCC k, Ob (a :: k), Ob b) => a ~> b || a
-- test1 = toCCC @(F a) @(F b + F a) (lam \x -> right x)
-- test2 :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => a && b ~> b && a
-- test2 = toCCC @(F a * F b) @(F b * F a) (lam \(x :& y) -> (y :& x))
-- test4 :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => a ~> b ~~> (a && b)
-- test4 = toCCC @(F a) @(F b --> F a * F b) (lam \x -> lam \y -> (x :& y))
-- test5 :: forall {k} (a :: k) b. (BiCCC k, Ob a, Ob b) => (a && b) ~> (b && a)
-- test5 = toCCC @(F a * F b) @(F b * F a) (lam \(a :& b) -> lam (\c -> (b :& c)) $ a)
-- test6 :: forall {k} a b c. (BiCCC k, Ob (a :: k), Ob b, Ob c) => b ~~> a ~~> b ~~> c ~> a ~~> b ~~> c
-- test6 = toCCC @(F b --> F a --> F b --> F c) @(F a --> F b --> F c) (lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z))))
-- test7 :: forall {k} a b. (BiCCC k, Ob (a :: k), Ob b) => (a || b) ~> (b || a)
-- test7 = toCCC @(F a + F b) @(F b + F a) (lam \x -> either (lam \y -> right y) (lam \y -> left y) $ x)
-- test8 :: forall {k} (a :: k) b c. (BiCCC k, Ob a, Ob b, Ob c) => a && (b || c) ~> (a && b) || (a && c)
-- test8 =
--   toCCC @(F a * (F b + F c)) @((F a * F b) + (F a * F c))
--     (lam \(a :& bc) -> either (lam \b -> lam \a' -> left (a' :& b)) (lam \c -> lam \a' -> right (a' :& c)) $ bc $ a)
