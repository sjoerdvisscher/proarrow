{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Free where

import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Core (CAT, Category, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, (:~>))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))

type MULTICAT k = [k] -> k -> Type

class ((a) => b) => a :=> b
instance ((a) => b) => a :=> b

newtype FREE (str :: Constraint) (p :: CAT k) = F (FK k)
type instance UN F (F k) = k

type Free :: CAT (FREE str p)
data Free a b where
  Free
    :: MFree str p ctx a
    -> Free (F (Flatten ctx)) (F a :: FREE str p)

data FK k = EMB k
type instance UN EMB (EMB a) = a

type MFree :: Constraint -> CAT k -> MULTICAT (FK k)
data MFree str p as b where
  Id :: (IsFK a) => MFree str p '[a] a
  Emb :: (Ob a, Ob b) => p a b -> MFree str p ctx (EMB a) -> MFree str p ctx (EMB b)
  Str :: (c :=> HasStructure str k, Structure str, IsFKs ctx, IsFK a) => str c p ctx a -> MFree c p ctx (a :: FK k)

withIsFKs :: MFree str p as b -> (IsFKs as => r) -> r
withIsFKs Id r = r
withIsFKs (Emb _ f) r = withIsFKs f r
withIsFKs Str{} r = r

mcomp :: MFree cstr p bs c -> MFree cstr p as (Flatten bs) -> MFree cstr p as c
mcomp Id g = g
mcomp (Emb p f) g = Emb p (mcomp f g)
mcomp (Str s) g = withIsFKs g (composeStructure s g)

type IsFK :: forall {k}. FK k -> Constraint
class IsFK (a :: FK k) where
  type Lower (a :: FK k) :: k
  withLowerOb :: ((Ob (Lower a)) => r) -> r
instance (Ob a) => IsFK (EMB a) where
  type Lower (EMB a) = a
  withLowerOb r = r

type IsFKs :: forall {k}. [FK k] -> Constraint
class IsFKs (as :: [FK k]) where
  type Flatten (as :: [FK k]) :: FK k
  withFlattenOb :: ((IsFK (Flatten as)) => r) -> r

instance (IsFK a) => IsFKs '[a] where
  type Flatten '[a] = a
  withFlattenOb r = r

class Structure (str :: (Constraint) -> CAT k -> MULTICAT (FK k)) where
  type HasStructure str :: Kind -> Constraint
  foldStructure
    :: forall (cat :: CAT k) (ctx :: [FK k]) (a :: FK k) (c :: Constraint) (p :: CAT k)
     . (HasStructure str k, Category cat)
    => (forall as b. MFree c p as b -> cat (Lower (Flatten as)) (Lower b))
    -> str c p ctx a
    -> cat (Lower (Flatten ctx)) (Lower a)
  composeStructure
    :: forall (ctx :: [FK k]) (c :: Constraint) (p :: CAT k) (as :: [FK k]) (b :: FK k)
     . (IsFKs as, IsFK b, c :=> HasStructure str k)
    => str c p ctx b
    -> MFree c p as (Flatten ctx)
    -> MFree c p as b

data Plain c p ctx1 ctx2
class NoConstraint k
instance NoConstraint k
instance Structure Plain where
  type HasStructure Plain = NoConstraint
  foldStructure _ = \case {}
  composeStructure = \case {}

data family TermF :: k
instance (HasTerminalObject k) => IsFK (TermF :: FK k) where
  type Lower TermF = TerminalObject
  withLowerOb r = r
instance (HasTerminalObject k) => IsFKs ('[] :: [FK k]) where
  type Flatten '[] = TermF
  withFlattenOb r = r
type Terminal :: Constraint -> CAT k -> MULTICAT (FK k)
data Terminal c p ctx a where
  Terminal :: (IsFKs ctx) => Terminal c p ctx TermF
instance Structure Terminal where
  type HasStructure Terminal = HasTerminalObject
  foldStructure _ (Terminal @ctx) = withFlattenOb @ctx (withLowerOb @(Flatten ctx) terminate)
  composeStructure Terminal _ = Str Terminal
instance (HasTerminalObject k) => HasTerminalObject (FREE c (p :: CAT k)) where
  type TerminalObject = F TermF
  terminate @(F a) = Free @_ @_ @'[a] (Str Terminal)

data family (*!) (a :: k) (b :: k) :: k
instance (HasBinaryProducts k, IsFK (a :: FK k), IsFK (b :: FK k)) => IsFK (a *! b) where
  type Lower (a *! b) = Lower a && Lower b
  withLowerOb r = withLowerOb @a (withLowerOb @b (withObProd @_ @(Lower a) @(Lower b) r))
instance (HasBinaryProducts k, IsFKs (b ': ctx), IsFK (a :: FK k)) => IsFKs (a ': b ': ctx) where
  type Flatten (a ': b ': ctx) = a *! Flatten (b ': ctx)
  withFlattenOb r = withFlattenOb @(b ': ctx) r
type Product :: Constraint -> CAT k -> MULTICAT (FK k)
data Product c p ctx a where
  Prd :: (IsFK a, IsFK b, IsFKs ctx) => MFree c p ctx a -> MFree c p ctx b -> Product c p ctx (a *! b)
  Fst :: forall a b ctx c p. (IsFK a, IsFK b, IsFKs ctx) => MFree c p ctx (a *! b) -> Product c p ctx a
  Snd :: forall a b ctx c p. (IsFK a, IsFK b, IsFKs ctx) => MFree c p ctx (a *! b) -> Product c p ctx b
instance Structure Product where
  type HasStructure Product = HasBinaryProducts
  foldStructure go (Prd f g) = go f &&& go g
  foldStructure go (Fst @a @b f) = withLowerOb @a (withLowerOb @b (fst @_ @(Lower a) @(Lower b) . go f))
  foldStructure go (Snd @a @b f) = withLowerOb @a (withLowerOb @b (snd @_ @(Lower a) @(Lower b) . go f))
  composeStructure (Prd f g) h = Str (Prd (mcomp f h) (mcomp g h))
  composeStructure (Fst f) g = Str (Fst (mcomp f g))
  composeStructure (Snd f) g = Str (Snd (mcomp f g))


fold
  :: forall {k} (str :: Constraint) (p :: CAT k) (cat :: CAT k) (a :: FK k) (b :: FK k)
   . (Category cat, str)
  => (p :~> cat)
  -> Free (F a :: FREE str p) (F b)
  -> cat (Lower a) (Lower b)
fold pn (Free f) = go f
  where
    go :: (cstr) => MFree cstr p as c -> cat (Lower (Flatten as)) (Lower c)
    go (Id @x) = withLowerOb @x id
    go (Emb p g) = pn p . go g
    go (Str s) = foldStructure go s

instance CategoryOf (FREE str p) where
  type (~>) = Free
  type Ob a = (Is F a, IsFK (UN F a))

instance Promonad (Free :: CAT (FREE str p)) where
  id = Free Id
  Free f . Free g = Free (mcomp f g)

instance Profunctor (Free :: CAT (FREE str p)) where
  dimap = dimapDefault
  r \\ Free Id = r
  r \\ Free (Emb _ f) = r \\ Free f
  r \\ Free (Str @_ @_ @_ @ctx _) = withFlattenOb @ctx r

data Test a b where
  Show :: Test P.Int P.String
  Read :: Test P.String P.Int
  Succ :: Test P.Int P.Int
  Dup :: Test P.String P.String

type T ctx = MFree () Test ctx
show :: T ctx (EMB P.Int) -> T ctx (EMB P.String)
show = Emb Show

read :: T ctx (EMB P.String) -> T ctx (EMB P.Int)
read = Emb Read

succ :: T ctx (EMB P.Int) -> T ctx (EMB P.Int)
succ = Emb Succ

dup :: T ctx (EMB P.String) -> T ctx (EMB P.String)
dup = Emb Dup

test :: T ctx (EMB P.String) -> T ctx (EMB P.String)
test x = dup (show (succ (read x)))

term :: (IsFKs ctx) => T ctx a -> T ctx TermF
term _ = Str Terminal

prd :: (IsFKs ctx, IsFK a, IsFK b) => T ctx a -> T ctx b -> T ctx (a *! b)
prd x y = Str (Prd x y)

test2 :: IsFKs ctx => T ctx (EMB P.String) -> T ctx (EMB P.String *! EMB P.String)
test2 x = prd x (test x)

testF :: Free (F (EMB P.String) :: FREE () Test) (F (EMB P.String *! EMB P.String))
testF = Free (test2 Id)

-- >>> testFold "123"
-- ("123","124124")
testFold :: P.String -> (P.String, P.String)
testFold = fold interp testF
  where
    interp :: Test :~> (->)
    interp Show = P.show
    interp Read = P.read
    interp Succ = P.succ
    interp Dup = \s -> s P.++ s
