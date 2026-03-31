{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Tools.Diagrams.Dot where

import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.List (cycle, repeat, sort)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Prelude
  ( Bool (..)
  , Either (..)
  , Eq (..)
  , Foldable
  , Functor (..)
  , Int
  , Num (..)
  , Ord (..)
  , Show
  , String
  , Traversable (..)
  , const
  , either
  , foldMap
  , show
  , snd
  , splitAt
  , zip
  , zip3
  , (!!)
  , ($)
  , (++)
  )

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (Costrong (..), MonoidalAction (..), Strong (..))
import Proarrow.Category.Monoidal.Strictified (IsList (..), SList (..), type (++))
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, obj)
import Proarrow.Monoid (Comonoid (..), CopyDiscard, Monoid (..))

type Port = String -- Basically a shown int, but may contain an additional direction (:n, :e, :s, :w)

newtype Vec as x = Vec {unVec :: [x]}
  deriving newtype (Show, Eq, Foldable, Functor)
instance Traversable (Vec as) where
  traverse f (Vec xs) = fmap Vec (traverse f xs)
newtype Fin as = Fin {unFin :: Int}
  deriving newtype (Show, Eq, Num)
(!) :: Vec as x -> Fin as -> x
Vec xs ! Fin i = xs !! i

(+++) :: Vec as x -> Vec bs x -> Vec (as ++ bs) x
Vec xs +++ Vec ys = Vec (xs ++ ys)

split :: (IsList as) => Vec (as ++ bs) x -> (Vec as x, Vec bs x)
split @as (Vec xs) = case splitAt (len @as) xs of (as, bs) -> (Vec as, Vec bs)

len :: (IsList as) => Int
len @as = case sList @as of
  SNil -> 0
  SSing -> 1
  SCons @_ @bs -> 1 + len @bs

ixs :: (IsList as) => Vec as (Fin as)
ixs @as = case sList @as of
  SNil -> Vec []
  SSing -> Vec [0]
  SCons @_ @bs -> coerce (0 : fmap (+ 1) (unVec (ixs @bs)))

ixed :: (IsList as) => Vec as x -> Vec as (Fin as, x)
ixed (Vec []) = Vec []
ixed (Vec (x : xs)) = Vec $ (0, x) : fmap (\(i, y) -> (i + 1, y)) (unVec (ixed (Vec xs)))

zipV3 :: Vec as x -> Vec as y -> Vec as z -> Vec as (x, y, z)
zipV3 (Vec xs) (Vec ys) (Vec zs) = Vec (zip3 xs ys zs)

relax :: forall bs as. Fin as -> Fin (as ++ bs)
relax (Fin i) = Fin i

shift :: forall as bs. (IsList as) => Fin bs -> Fin (as ++ bs)
shift (Fin i) = Fin (len @as + i)

eitherF :: forall as bs r. (IsList as) => (Fin as -> r) -> (Fin bs -> r) -> Fin (as ++ bs) -> r
eitherF f g (Fin i)
  | i < len @as = f (Fin i)
  | True = g (Fin (i - len @as))

names :: (IsList (as :: [Symbol])) => Vec as String
names @as = case sList @as of
  SNil -> Vec []
  SSing @s -> Vec [symbolVal (Proxy @s)]
  SCons @s @ss -> Vec (symbolVal (Proxy @s) : unVec (names @ss))

type SymRefl :: CAT Symbol
data SymRefl a b where
  SymRefl :: (KnownSymbol s) => SymRefl s s
instance Eq (SymRefl a b) where
  SymRefl == SymRefl = True
instance Show (SymRefl a b) where
  show SymRefl = "SymRefl"
instance Profunctor SymRefl where
  dimap = dimapDefault
  r \\ SymRefl = r
instance Promonad SymRefl where
  id = SymRefl
  SymRefl . SymRefl = SymRefl
instance CategoryOf Symbol where
  type (~>) = SymRefl
  type Ob s = KnownSymbol s

type DOT :: Kind
type data DOT = D [Symbol]
type instance UN D (D ss) = ss

data DotData as bs = DotData
  { inputs :: Vec as (Either (Fin bs) Port)
  , outputs :: Vec bs (Either (Fin as) Port)
  , edges :: [(Port, String, Port)]
  , nodeOpts :: [String]
  }
  deriving (Show, Eq)

type Dot :: CAT DOT
data Dot a b where
  Dot :: (IsList as, IsList bs) => (Int -> (Int, DotData as bs)) -> Dot (D as) (D bs)

instance Eq (Dot a b) where
  Dot f == Dot g = normalize (getData (Dot f)) == normalize (getData (Dot g))
instance Show (Dot a b) where
  show (Dot f) = show (getData (Dot f))

instance Profunctor Dot where
  dimap = dimapDefault
  r \\ Dot{} = r
instance Promonad Dot where
  id @(D as) = Dot \n ->
    ( n
    , DotData
        { inputs = fmap Left (ixs @as)
        , outputs = fmap Left (ixs @as)
        , edges = []
        , nodeOpts = []
        }
    )
  Dot @bs l . Dot r = Dot \i ->
    let (k, DotData li lo le ln) = l j; (j, DotData ri ro re rn) = r i
    in ( k
       , DotData
           { inputs = fmap (either (li !) Right) ri
           , outputs = fmap (either (ro !) Right) lo
           , edges = re ++ foldMap (\case (Right n1, n, Right n2) -> [(n1, n, n2)]; _ -> []) (zipV3 ro (names @bs) li) ++ le
           , nodeOpts = rn ++ ln
           }
       )
instance CategoryOf DOT where
  type (~>) = Dot
  type Ob a = (Is D a, IsList (UN D a))

instance MonoidalProfunctor Dot where
  par0 = Dot \i -> (i, DotData (Vec []) (Vec []) [] [])
  Dot @lis @los l `par` Dot @ris @ros r = withIsList2 @lis @ris $ withIsList2 @los @ros $ Dot \i ->
    let (k, DotData li lo le ln) = l j; (j, DotData ri ro re rn) = r i
    in ( k
       , DotData
           { inputs = fmap (first (relax @ros)) li +++ fmap (first (shift @los)) ri
           , outputs = fmap (first (relax @ris)) lo +++ fmap (first (shift @lis)) ro
           , edges = le ++ re
           , nodeOpts = ln ++ rn
           }
       )
instance Monoidal DOT where
  type Unit = D '[]
  type ls ** rs = D (UN D ls ++ UN D rs)
  withOb2 @(D ls) @(D rs) r = withIsList2 @ls @rs r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @as @bs @cs = obj @as `par` obj @bs `par` obj @cs
  associatorInv @as @bs @cs = obj @as `par` obj @bs `par` obj @cs
instance SymMonoidal DOT where
  swap @(D as) @(D bs) =
    withIsList2 @as @bs $
      withIsList2 @bs @as $
        Dot \n ->
          let as = ixs @as; bs = ixs @bs
          in ( n
             , DotData
                 { inputs = fmap Left (fmap (shift @bs) as +++ fmap (relax @as) bs)
                 , outputs = fmap Left (fmap (shift @as) bs +++ fmap (relax @bs) as)
                 , edges = []
                 , nodeOpts = []
                 }
             )
instance (Ob as) => Monoid (D as) where
  mempty = node' (Vec []) (Vec (cycle [":s"])) "shape=point; width=0.07; fillcolor=white"
  mappend =
    withIsList2 @as @as $ node' (Vec (cycle [":nw", ":ne"])) (Vec (cycle [":s"])) "shape=point; width=0.07; fillcolor=white"
instance (Ob as) => Comonoid (D as) where
  counit = node' (Vec (cycle [":n"])) (Vec []) "shape=point; width=0.07"
  comult = withIsList2 @as @as $ node' (Vec (cycle [":n"])) (Vec (cycle [":sw", ":se"])) "shape=point; width=0.07"
instance CopyDiscard DOT
instance Strong DOT Dot where
  act = par
instance Costrong DOT Dot where
  coact @(D as) @(D xs) @(D ys) (Dot f) = Dot \n ->
    case f n of
      (n', DotData is os es ns) ->
        let
          inps = fmap fromI is
          outs = fmap fromO os
          (ais, xs) = split @as @xs inps
          (aos, ys) = split @as @ys outs
          fromI = either (eitherF @as @ys (ais !) Left) Right
          fromO = either (eitherF @as @xs (aos !) Left) Right
        in
          ( n'
          , DotData
              { inputs = xs
              , outputs = ys
              , edges =
                  es ++ foldMap (\case (Right n1, nm, Right n2) -> [(n1 ++ ":sw", nm, n2 ++ ":nw")]; _ -> []) (zipV3 aos (names @as) ais)
              , nodeOpts = ns
              }
          )
instance MonoidalAction DOT DOT where
  type Act a x = a ** x
  withObAct @a @x r = withOb2 @_ @a @x r
  unitor = id
  unitorInv = id
  multiplicator @as @bs @cs = obj @as `par` obj @bs `par` obj @cs
  multiplicatorInv @as @bs @cs = obj @as `par` obj @bs `par` obj @cs

swap2 :: (Ob a, Ob b) => Dot (D [a, b]) (D [b, a])
swap2 @a @b = swap @_ @(D '[a]) @(D '[b])

-- Regular swap won't render a crossing, since dot can freely move the edges around.
-- This version forces a crossing by adding an invisible node.
swapNode :: (Ob a, Ob b) => Dot (D [a, b]) (D [b, a])
swapNode @a @b =
  node' @[a, b] @[b, a]
    (Vec [":nw", ":ne"])
    (Vec [":sw", ":se"])
    "shape=point; style=invis; height=0; width=0"

node' :: (IsList as, IsList bs) => Vec as String -> Vec bs String -> String -> Dot (D as) (D bs)
node' @as @bs as bs s = Dot \n ->
  ( n + 1
  , DotData
      { inputs = fmap (\i -> Right (show n ++ (as ! i))) (ixs @as)
      , outputs = fmap (\i -> Right (show n ++ (bs ! i))) (ixs @bs)
      , edges = []
      , nodeOpts = [s]
      }
  )

node :: (IsList as, IsList bs) => String -> Dot (D as) (D bs)
node s = node' (Vec (repeat "")) (Vec (repeat "")) ("label=\"" ++ s ++ "\"")

line :: (Ob a) => Dot (D '[a]) (D '[a])
line = id

getData :: Dot (D as) (D bs) -> DotData as bs
getData (Dot f) = snd (f 0)

normalize :: DotData as bs -> DotData as bs
normalize (DotData is os es ns) =
  DotData is os (sort es) (sort ns)

run :: Dot (D as) (D bs) -> String
run @as @bs (Dot f) =
  let (_, DotData is os es ns) = f 0; as = ixed (names @as); bs = ixed (names @bs)
  in "digraph G { ranksep=1; node [fontname=\"Times-Italic\"; shape=circle; margin=0]; edge [fontname=\"Times-Italic\"; dir=none];"
       -- fix inputs at the top
       ++ "\n  { rank=source; "
       ++ foldMap
         (\(i, n) -> "\n    i" ++ show i ++ " [label=\"" ++ n ++ "\"; shape=plain];")
         as
       ++ "}"
       -- fix outputs at the bottom
       ++ "\n  { rank=sink; "
       ++ foldMap
         (\(i, n) -> "\n    o" ++ show i ++ " [label=\"" ++ n ++ "\"; shape=plain];")
         bs
       ++ "}"
       -- node configuration
       ++ foldMap (\(i, n) -> "\n  " ++ show i ++ " [" ++ n ++ "];") (zip [0 :: Int ..] ns)
       -- edges from inputs
       ++ foldMap (\(i, n) -> "\n  i" ++ show i ++ ":s -> " ++ either (\j -> "o" ++ show j ++ ":n") id n ++ ";") (ixed is)
       -- edges from outputs
       ++ foldMap (\(i, n) -> either (const "") (\n' -> "\n  " ++ n' ++ " -> o" ++ show i ++ ":n;") n) (ixed os)
       -- internal edges
       ++ foldMap (\(i, s, j) -> "\n  " ++ i ++ " -> " ++ j ++ " [label=\"" ++ s ++ "\"];") es
       ++ "\n}\n"

unitAdj :: (Ob l, Ob r) => Dot (D '[]) (D '[l, r])
unitAdj = node' (Vec []) (Vec [":sw", ":se"]) "label=η"

counitAdj :: (Ob l, Ob r) => Dot (D '[r, l]) (D '[])
counitAdj = node' (Vec [":nw", ":ne"]) (Vec []) "label=ϵ"
