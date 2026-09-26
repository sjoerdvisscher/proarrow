{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | String diagrams drawn as SVG. 'Svg' is the category of diagrams of
-- "Proarrow.Tools.Diagrams.Dot", with the same meaning, but a diagram is laid out from how it is
-- built instead of by Graphviz: a tensor puts its two sides next to each other, a composite stacks
-- them with a band of curved wires in between, and a trace draws its loops around the side. Every
-- coordinate is computed here, so every choice can be tweaked.
--
-- Unlike 'DOT', 'SVG' is not strict about its unit: the unit is a wire of its own, 'I', so the
-- unitors are arrows that can be drawn, a dotted wire ending on or leaving another wire. With
-- 'explicitCoherence' off, unit wires take up no room and are not drawn at all.
--
-- Nor is 'SVG' self-dual on the nose: the dual of a wire @'Wire' s@ is the wire @'Co' s@, shown
-- with a superscript ⁻¹ and drawn as a hollow line. The arrows between a wire and its dual only
-- relabel.
--
-- Both are only drawn: an arrow means the 'Dot' diagram on the wires with the unit wires left out
-- and the duals forgotten ('Erase').
module Proarrow.Tools.Diagrams.Svg where

import Data.Functor.Identity (Identity (..))
import Data.Kind (Constraint)
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Numeric (showFFloat)
import Prelude hiding (Monoid (..), curry, id, (**), (.))

import Proarrow.Category.Instance.Free (All)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, Hypergraph, cap, cup)
import Proarrow.Category.Monoidal.StarAutonomous (ExpSA, StarAutonomous (..), applySA, currySA, expSA)
import Proarrow.Category.Monoidal.Strength (Costrong (..))
import Proarrow.Category.Monoidal.Strictified
  ( IsList (..)
  , SList (..)
  , Strictified (..)
  , obj1
  , singleton
  , swap2
  , type (++)
  )
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN, dimapDefault, obj)
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid (..), Monoid (..))
import Proarrow.Tools.Diagrams.Dot (DOT, Dot)
import Proarrow.Tools.Diagrams.Dot qualified as Dot
import Proarrow.Tools.Laws (Equation (..), Labelled (..), Law (..), Laws (..), lawName)

-- * Wires

-- | A wire: a labelled wire, the dual of one, or the unit wire.
type W :: Kind
type data W = Wire Symbol | Co Symbol | I

-- | The dual of a wire. The unit wire is its own dual.
type DualW :: W -> W
type family DualW w where
  DualW (Wire s) = Co s
  DualW (Co s) = Wire s
  DualW I = I

-- | The duals of the wires.
type DualList :: [W] -> [W]
type family DualList ws where
  DualList '[] = '[]
  DualList (w ': ws) = DualW w ': DualList ws

-- | The labels of the wires that carry something: the unit wires left out, and a dual wire
-- labelled as the wire it is the dual of.
type Erase :: [W] -> [Symbol]
type family Erase ws where
  Erase '[] = '[]
  Erase (Wire s ': ws) = s ': Erase ws
  Erase (Co s ': ws) = s ': Erase ws
  Erase (I ': ws) = Erase ws

-- | A wire whose label is known. The methods are facts about 'DualW' and 'Erase' that hold for
-- each kind of wire, from which 'withIsListDual', 'withIsListErase', 'withEraseAppend',
-- 'withDualDual' and 'withEraseDual' prove them for lists by induction.
type KnownWire :: W -> Constraint
class KnownWire w where
  -- | The label of the wire as it is shown, and its kind.
  wireInfo :: (String, WireKind)

  withKnownDualW :: ((KnownWire (DualW w)) => r) -> r
  withIsListEraseCons :: forall (ws :: [W]) r. (IsList (Erase ws)) => ((IsList (Erase (w ': ws))) => r) -> r
  withEraseAppendCons
    :: forall (as :: [W]) (bs :: [W]) r
     . (Erase (as ++ bs) ~ (Erase as ++ Erase bs))
    => ((Erase (w ': (as ++ bs)) ~ (Erase (w ': as) ++ Erase bs)) => r)
    -> r
  withDualDualW :: ((DualW (DualW w) ~ w) => r) -> r
  withEraseDualCons
    :: forall (ws :: [W]) r. (Erase (DualList ws) ~ Erase ws) => ((Erase (DualList (w ': ws)) ~ Erase (w ': ws)) => r) -> r

instance (KnownSymbol s) => KnownWire (Wire s) where
  wireInfo = (symbolVal (Proxy @s), Plain)
  withKnownDualW r = r
  withIsListEraseCons @ws r = withIsList2 @'[s] @(Erase ws) r
  withEraseAppendCons r = r
  withDualDualW r = r
  withEraseDualCons r = r

instance (KnownSymbol s) => KnownWire (Co s) where
  wireInfo = (symbolVal (Proxy @s) ++ "⁻¹", DualWire)
  withKnownDualW r = r
  withIsListEraseCons @ws r = withIsList2 @'[s] @(Erase ws) r
  withEraseAppendCons r = r
  withDualDualW r = r
  withEraseDualCons r = r

instance KnownWire I where
  wireInfo = ("𝐈", UnitWire)
  withKnownDualW r = r
  withIsListEraseCons r = r
  withEraseAppendCons r = r
  withDualDualW r = r
  withEraseDualCons r = r

type WireId :: CAT W
data WireId a b where
  WireId :: (KnownWire w) => WireId w w
instance Profunctor WireId where
  dimap = dimapDefault
  r \\ WireId = r
instance Promonad WireId where
  id = WireId
  WireId . WireId = WireId

-- | The discrete category on wires, so that lists of wires are objects of 'Strictified'.
instance CategoryOf W where
  type (~>) = WireId
  type Ob w = KnownWire w

-- | The duals of a list of wires are a list of wires.
withIsListDual :: forall (ws :: [W]) r. (IsList ws) => ((IsList (DualList ws)) => r) -> r
withIsListDual r =
  listCase @ws
    r
    (\ @w -> withKnownDualW @w r)
    (\ @b @bs @c @cs -> withKnownDualW @b (withKnownDualW @c (withIsListDual @cs (withIsListDual @bs r))))

-- | The erased wires of a list of wires are a list of labels.
withIsListErase :: forall (ws :: [W]) r. (IsList ws) => ((IsList (Erase ws)) => r) -> r
withIsListErase r =
  listCase @ws
    r
    (\ @w -> withIsListEraseCons @w @'[] r)
    (\ @w @ws' -> withIsListErase @ws' (withIsListEraseCons @w @ws' r))

-- | Erasing commutes with appending.
withEraseAppend
  :: forall (as :: [W]) (bs :: [W]) r. (IsList as) => ((Erase (as ++ bs) ~ (Erase as ++ Erase bs)) => r) -> r
withEraseAppend r =
  listCase @as
    r
    (\ @w -> withEraseAppendCons @w @'[] @bs r)
    (\ @w @as' -> withEraseAppend @as' @bs (withEraseAppendCons @w @as' @bs r))

-- | Dualising twice gives the wires back.
withDualDual :: forall (ws :: [W]) r. (IsList ws) => ((DualList (DualList ws) ~ ws) => r) -> r
withDualDual r =
  listCase @ws
    r
    (\ @w -> withDualDualW @w r)
    (\ @w @ws' -> withDualDual @ws' (withDualDualW @w r))

-- | Dualising commutes with appending.
withDualAppend
  :: forall (as :: [W]) (bs :: [W]) r. (IsList as) => ((DualList (as ++ bs) ~ (DualList as ++ DualList bs)) => r) -> r
withDualAppend r = listCase @as r r (\ @_ @as' -> withDualAppend @as' @bs r)

-- | The duals of wires erase to the same labels as the wires.
withEraseDual :: forall (ws :: [W]) r. (IsList ws) => ((Erase (DualList ws) ~ Erase ws) => r) -> r
withEraseDual r =
  listCase @ws
    r
    (\ @w -> withEraseDualCons @w @'[] r)
    (\ @w @ws' -> withEraseDual @ws' (withEraseDualCons @w @ws' r))

-- | The labels of the wires of @ws@ as they are shown, and their kinds.
wires :: forall (ws :: [W]). (IsList ws) => [(String, WireKind)]
wires = case sList @ws of
  SNil -> []
  SSing @w -> [wireInfo @w]
  SCons @w @ws' -> wireInfo @w : wires @ws'

wireKinds :: forall (ws :: [W]). (IsList ws) => [WireKind]
wireKinds = map snd (wires @ws)

-- * The category

type SVG :: Kind
type data SVG = S [W]

-- | A diagram: its meaning, as a 'Dot' diagram on the erased wires, and how it was built, which
-- is drawn when it is rendered.
type Svg :: CAT SVG
data Svg a b where
  Svg :: (IsList as, IsList bs) => Dot (Dot.D (Erase as)) (Dot.D (Erase bs)) -> Diagram -> Svg (S as) (S bs)

-- | A diagram from its meaning, which may use that the erased wires are lists, and how it is
-- drawn.
svg
  :: forall (as :: [W]) (bs :: [W])
   . (IsList as, IsList bs)
  => ((IsList (Erase as), IsList (Erase bs)) => Dot (Dot.D (Erase as)) (Dot.D (Erase bs)))
  -> Diagram
  -> Svg (S as) (S bs)
svg d = withIsListErase @as (withIsListErase @bs (Svg d))

-- | A diagram that means the identity on the erased wires, drawn as given.
drawnAs :: forall (as :: [W]) (bs :: [W]). (IsList as, IsList bs, Erase as ~ Erase bs) => Diagram -> Svg (S as) (S bs)
drawnAs = svg @as @bs (obj @(Dot.D (Erase as)))

-- | An arrow between wires that erase to the same labels, a wire and its dual for example: in
-- meaning the identity. It is drawn as nothing, the wires carrying on in the style of their new
-- kinds.
relabel :: forall (a :: SVG) (b :: SVG). (Ob a, Ob b, Erase (UN S a) ~ Erase (UN S b)) => a ~> b
relabel = drawnAs (Straight (wireKinds @(UN S a)) (wireKinds @(UN S b)))

-- | Choices about what to draw.
data Options = Options
  { explicitIdentities :: Bool
  -- ^ draw each identity, 'line' included, as a wire in a dashed frame; otherwise an identity is
  -- not drawn at all
  , explicitCoherence :: Bool
  -- ^ draw the unit wires dotted, the unitors as a unit wire running into another wire or out of
  -- it, and the associators with brackets for the groupings they go between; otherwise none of
  -- these are drawn, and unit wires take up no room
  , explicitSwaps :: Bool
  -- ^ draw each 'swap' as a crossing of its own; otherwise its crossing is drawn in the band
  -- where the wires next change position
  , fixedSpiders :: Bool
  -- ^ keep the two legs of a copy or merge point in the order they are listed; otherwise they
  -- may trade places to avoid a crossing, which the points being commutative allows
  }
  deriving (Show)

-- | Nothing drawn that the meaning does not need, legs in order.
defaultOptions :: Options
defaultOptions = Options{explicitIdentities = False, explicitCoherence = False, explicitSwaps = False, fixedSpiders = True}

-- | The meaning of a diagram, forgetting how it is drawn.
meaningOf :: Svg (S as) (S bs) -> Dot (Dot.D (Erase as)) (Dot.D (Erase bs))
meaningOf (Svg d _) = d

instance Show (Svg a b) where
  show (Svg d _) = show d

instance Profunctor Svg where
  dimap = dimapDefault
  r \\ Svg{} = r
instance Promonad Svg where
  id @(S as) = drawnAs @as @as (Ident (wireKinds @as))
  Svg f l . Svg g m = Svg (f . g) (Seq m l)

-- | The category string diagrams are drawn in: an object @'S' ws@ is the list of wires along a
-- boundary.
instance CategoryOf SVG where
  type (~>) = Svg
  type Ob a = (Is S a, IsList (UN S a))

instance MonoidalProfunctor Svg where
  one = drawnAs (Ident [UnitWire])
  Svg @lis @los f l ** Svg @ris @ros g m =
    withIsList2 @lis @ris $
      withIsList2 @los @ros $
        withEraseAppend @lis @ris $
          withEraseAppend @los @ros $
            Svg (f ** g) (Beside l m)

-- | The unit is the unit wire, and the unitors absorb or create it.
instance Monoidal SVG where
  type Unit = S '[I]
  type ls ** rs = S (UN S ls ++ UN S rs)
  withOb2 @(S ls) @(S rs) r = withIsList2 @ls @rs r
  leftUnitor @(S as) = withIsList2 @'[I] @as $ drawnAs (Unitor OnLeft Absorb (wireKinds @as))
  leftUnitorInv @(S as) = withIsList2 @'[I] @as $ drawnAs (Unitor OnLeft Create (wireKinds @as))
  rightUnitor @(S as) = withRightUnit @as $ drawnAs (Unitor OnRight Absorb (wireKinds @as))
  rightUnitorInv @(S as) = withRightUnit @as $ drawnAs (Unitor OnRight Create (wireKinds @as))
  associator @(S as) @(S bs) @(S cs) = rebracketed @as @bs @cs LeftFirst
  associatorInv @(S as) @(S bs) @(S cs) = rebracketed @as @bs @cs RightFirst

-- | Wires with a unit wire on the right are a list, and erase to the same labels.
withRightUnit :: forall (as :: [W]) r. (IsList as) => ((IsList (as ++ '[I]), Erase (as ++ '[I]) ~ Erase as) => r) -> r
withRightUnit r = withIsList2 @as @'[I] $ withEraseAppend @as @'[I] $ withIsListErase @as r

-- | An associator, from the given grouping to the other one.
rebracketed
  :: forall (as :: [W]) (bs :: [W]) (cs :: [W])
   . (IsList as, IsList bs, IsList cs)
  => Grouping
  -> Svg (S (as ++ (bs ++ cs))) (S (as ++ (bs ++ cs)))
rebracketed g =
  withIsList2 @bs @cs $
    withIsList2 @as @(bs ++ cs) $
      drawnAs (Rebracket g (wireKinds @as) (wireKinds @bs) (wireKinds @cs))

instance SymMonoidal SVG where
  swap @(S as) @(S bs) =
    withIsList2 @as @bs $
      withIsList2 @bs @as $
        withEraseAppend @as @bs $
          withEraseAppend @bs @as $
            withIsListErase @as $
              withIsListErase @bs $
                svg (swap @DOT @(Dot.D (Erase as)) @(Dot.D (Erase bs))) $
                  Permute False (wireKinds @(as ++ bs)) ([Dot.len @as .. Dot.len @as + Dot.len @bs - 1] ++ [0 .. Dot.len @as - 1])

-- | The unit point takes the unit wire in, and the discard point gives it out.
instance (Ob as) => Monoid (S as) where
  mempty = svg (mempty @(Dot.D (Erase as))) (Seq UnitEnd (Points UnitPoint (wireKinds @as)))
  mappend = withIsList2 @as @as $ withEraseAppend @as @as $ svg (mappend @(Dot.D (Erase as))) (Points MergePoint (wireKinds @as))

instance (Ob as) => Comonoid (S as) where
  counit = svg (counit @(Dot.D (Erase as))) (Seq (Points DiscardPoint (wireKinds @as)) UnitStart)
  comult = withIsList2 @as @as $ withEraseAppend @as @as $ svg (comult @(Dot.D (Erase as))) (Points CopyPoint (wireKinds @as))
instance (Ob as) => CocommutativeComonoid (S as)
instance (Ob as) => CommutativeMonoid (S as)
instance (Ob as) => Frobenius (S as)
instance CopyDiscard SVG
instance Hypergraph SVG

-- | The exponential is the *-autonomous one, @'Dual' (a '**' 'Dual' b)@, so curried wires show as
-- duals.
instance Closed SVG where
  type a ~~> b = ExpSA a b
  withObExp @a @b r = withObDual @SVG @b $ withOb2 @SVG @a @(Dual b) $ withObDual @SVG @(a ** Dual b) r
  curry @a @b @c = currySA @a @b @c
  apply @b @c = applySA @b @c
  (^^^) = expSA

-- | The dual of a wire is its 'Co' wire. Duals come from 'dualCup' and 'dualCap', which mean a cup
-- or cap and are drawn as a bend, so a dual wire is drawn hollow wherever it runs.
instance StarAutonomous SVG where
  type Dual a = S (DualList (UN S a))
  withObDual @a r = withIsListDual @(UN S a) r
  dual @a @b f =
    ( withObDual @SVG @a $
        withObDual @SVG @b $
          unStr @'[Dual b] @'[Dual a] $
            obj1 ** dualCupS @a
              M.== obj1 ** singleton f ** obj1
              M.== dualCapS @b ** obj1
    )
      \\ f
  dualInv @a @b g =
    withObDual @SVG @a $
      withObDual @SVG @b $
        unStr @'[b] @'[a] $
          dualCupS @a ** obj1
            M.== obj1 ** singleton g ** obj1
            M.== obj1 ** dualCapS @b
  linDist @a @b @c f =
    withObDual @SVG @b $
      withObDual @SVG @c $
        withOb2 @SVG @b @c $
          withObDual @SVG @(b ** c) $
            withOb2 @SVG @(Dual b) @(Dual c) $
              withDualAppend @(UN S b) @(UN S c) $
                relabel @(Dual b ** Dual c) @(Dual (b ** c))
                  . unStr @'[a] @[Dual b, Dual c]
                    ( obj1 ** dualCupS @b
                        M.== Str @[a, b] @'[Dual c] f ** obj1
                        M.== swap2
                    )
  linDistInv @a @b @c g =
    withObDual @SVG @b $
      withObDual @SVG @c $
        withOb2 @SVG @b @c $
          withObDual @SVG @(b ** c) $
            withOb2 @SVG @(Dual b) @(Dual c) $
              withDualAppend @(UN S b) @(UN S c) $
                unStr @[a, b] @'[Dual c] $
                  Str @'[a] @[Dual b, Dual c] (relabel @(Dual (b ** c)) @(Dual b ** Dual c) . g) ** obj1
                    M.== obj1 ** swap2
                    M.== dualCapS @b ** obj1
  doubleNeg @a = withObDual @SVG @a $ withObDual @SVG @(Dual a) $ withDualDual @(UN S a) $ relabel @(Dual (Dual a)) @a
  doubleNegInv @a = withObDual @SVG @a $ withObDual @SVG @(Dual a) $ withDualDual @(UN S a) $ relabel @a @(Dual (Dual a))

-- | A wire bent upwards, @a@ on the left and its dual on the right. It means 'cup', and is drawn
-- as one bend that turns into the dual at its apex.
dualCup :: forall (a :: SVG). (Ob a) => Unit ~> a ** Dual a
dualCup = withObDual @SVG @a $
  withEraseDual @(UN S a) $
    withOb2 @SVG @a @a $
      withOb2 @SVG @a @(Dual a) $
        case (obj @a ** relabel @a @(Dual a)) . cup @a of
          Svg d _ -> Svg d (Seq UnitEnd (Bend Cup (wireKinds @(UN S a)) (wireKinds @(UN S (Dual a)))))

-- | A wire bent downwards, the dual of @a@ on the left and @a@ on the right. It means 'cap', and is
-- drawn as one bend that turns into the dual at its apex.
dualCap :: forall (a :: SVG). (Ob a) => Dual a ** a ~> Unit
dualCap = withObDual @SVG @a $
  withEraseDual @(UN S a) $
    withOb2 @SVG @a @a $
      withOb2 @SVG @(Dual a) @a $
        case cap @a . (relabel @(Dual a) @a ** obj @a) of
          Svg d _ -> Svg d (Seq (Bend Cap (wireKinds @(UN S a)) (wireKinds @(UN S (Dual a)))) UnitStart)

-- | 'dualCup' as a strictified arrow. The *-autonomous structure is built from it, not from the
-- compact closed 'dualityUnit', so that the laws relating the two compare different definitions.
dualCupS :: forall (a :: SVG). (Ob a) => '[] ~> [a, Dual a]
dualCupS = withObDual @SVG @a $ Str (dualCup @a)

-- | 'dualCap' as a strictified arrow.
dualCapS :: forall (a :: SVG). (Ob a) => [Dual a, a] ~> '[]
dualCapS = withObDual @SVG @a $ Str (dualCap @a)

instance CompactClosed SVG where
  distribDual @a @b =
    withOb2 @SVG @a @b $
      withObDual @SVG @a $
        withObDual @SVG @b $
          withObDual @SVG @(a ** b) $
            withOb2 @SVG @(Dual a) @(Dual b) $
              withDualAppend @(UN S a) @(UN S b) $
                relabel @(Dual (a ** b)) @(Dual a ** Dual b)
  dualUnit = relabel
  dualityUnit @a = dualCup @a
  dualityCounit @a = dualCap @a

-- | The traced wires loop round the side of the diagram they are nearest to.
instance Costrong Tensor Svg where
  coact @(S as) @(S xs) @(S ys) (Svg f l) =
    withEraseAppend @as @xs $
      withEraseAppend @as @ys $
        withIsListErase @as $
          svg (coact @Tensor @Dot @(Dot.D (Erase as)) @(Dot.D (Erase xs)) @(Dot.D (Erase ys)) f) (Trace (wireKinds @as) l)

-- | Derived operations are drawn as what they are made of.
instance Labelled SVG where
  label _ f = f

-- * Building diagrams

-- | A box with the given name, its inputs along the top and its outputs along the bottom, each
-- output labelled with its wire.
node :: forall (as :: [W]) (bs :: [W]). (IsList as, IsList bs) => String -> Svg (S as) (S bs)
node s = svg (Dot.node @(Erase as) @(Erase bs) s) (Node s (wireKinds @as) (wires @bs))

-- | A wire, the identity on it.
line :: (KnownSymbol a) => Svg (S '[Wire a]) (S '[Wire a])
line = id

-- | A crossing of fixed height. A plain 'swap' is drawn as a crossing too, but in the band where
-- the wires next change position.
swapNode
  :: forall (a :: Symbol) (b :: Symbol). (KnownSymbol a, KnownSymbol b) => Svg (S [Wire a, Wire b]) (S [Wire b, Wire a])
swapNode = Svg (Dot.swapNode @a @b) (Permute True (wireKinds @[Wire a, Wire b]) [1, 0])

-- | The unit of an adjunction, drawn as a box named η.
unitAdj :: forall (l :: Symbol) (r :: Symbol). (KnownSymbol l, KnownSymbol r) => Svg (S '[]) (S '[Wire l, Wire r])
unitAdj = Svg (Dot.unitAdj @l @r) (Node "η" [] (wires @[Wire l, Wire r]))

-- | The counit of an adjunction, drawn as a box named ϵ.
counitAdj :: forall (l :: Symbol) (r :: Symbol). (KnownSymbol l, KnownSymbol r) => Svg (S '[Wire r, Wire l]) (S '[])
counitAdj = Svg (Dot.counitAdj @l @r) (Node "ϵ" (wireKinds @[Wire r, Wire l]) [])

-- | What kind of wire a wire is, which decides how it is drawn.
data WireKind = Plain | UnitWire | DualWire
  deriving (Eq, Show)

-- * Diagrams

-- | How a diagram was built. The options come in only when it is drawn: 'hideUnits' takes out what
-- 'explicitCoherence' would show, and 'layout' decides the rest.
data Diagram
  = -- | the identity on wires of the given kinds
    Ident [WireKind]
  | -- | wires of the given kinds, output @j@ continuing input @p !! j@; when the flag is set, its
    -- crossings are drawn on their own
    Permute Bool [WireKind] [Int]
  | -- | wires carrying straight on, as many out as in, possibly of other kinds
    Straight [WireKind] [WireKind]
  | -- | a box with a name, the kinds of its inputs, and the labels and kinds of its outputs
    Node String [WireKind] [(String, WireKind)]
  | -- | a point of the given kind on each wire
    Points PointKind [WireKind]
  | -- | bends joining each wire of the first kinds to its dual, of the second kinds
    Bend BendKind [WireKind] [WireKind]
  | -- | an associator from the given grouping, on three lists of wires
    Rebracket Grouping [WireKind] [WireKind] [WireKind]
  | -- | a unitor on wires of the given kinds
    Unitor Side Direction [WireKind]
  | -- | a unit wire ending
    UnitEnd
  | -- | a unit wire starting
    UnitStart
  | -- | the first diagram above the second
    Seq Diagram Diagram
  | -- | two diagrams side by side
    Beside Diagram Diagram
  | -- | the first inputs and outputs, of the given kinds, fed back
    Trace [WireKind] Diagram
  deriving (Show)

-- | The points a (co)monoid is drawn with.
data PointKind = UnitPoint | DiscardPoint | CopyPoint | MergePoint
  deriving (Show)

-- | Whether a bend opens downwards, a cup, or upwards, a cap.
data BendKind = Cup | Cap
  deriving (Show)

-- | Which pair an associator groups first: @(a ⊗ b) ⊗ c@ or @a ⊗ (b ⊗ c)@.
data Grouping = LeftFirst | RightFirst
  deriving (Show)

-- | Which side of the other wires a unit wire joins them.
data Side = OnLeft | OnRight
  deriving (Show)

-- | Whether a unitor ends a unit wire on another wire, or starts one from it.
data Direction = Absorb | Create
  deriving (Show)

-- | The diagram with its unit wires left out, and its unitors and associators turned into wires
-- carrying straight on.
hideUnits :: Diagram -> Diagram
hideUnits = \case
  Ident ks -> Ident (noUnits ks)
  Permute c ks p ->
    let kept = [i | (i, k) <- zip [0 :: Int ..] ks, k /= UnitWire]
        renumber i = fromMaybe 0 (List.elemIndex i kept)
    in Permute c (map (ks !!) kept) [renumber i | i <- p, ks !! i /= UnitWire]
  Straight ks ls -> Straight (noUnits ks) (noUnits ls)
  Node s ks os -> Node s (noUnits ks) [w | w@(_, k) <- os, k /= UnitWire]
  Points pk ks -> Points pk (noUnits ks)
  Bend b ka kd -> Bend b (noUnits ka) (noUnits kd)
  Rebracket _ ka kb kc -> straight (noUnits (ka ++ kb ++ kc))
  Unitor _ _ ks -> straight (noUnits ks)
  UnitEnd -> straight []
  UnitStart -> straight []
  Seq a b -> Seq (hideUnits a) (hideUnits b)
  Beside a b -> Beside (hideUnits a) (hideUnits b)
  Trace ks d -> Trace (noUnits ks) (hideUnits d)
  where
    straight ks = Straight ks ks

noUnits :: [WireKind] -> [WireKind]
noUnits = filter (/= UnitWire)

-- | The diagram laid out with the given options.
layout :: Options -> Diagram -> Layout
layout o = go . if explicitCoherence o then id else hideUnits
  where
    go = \case
      Ident ks -> identity (explicitIdentities o) ks
      Permute c ks p -> permutation (c || explicitSwaps o) ks p
      Straight ks ls -> Wiring [0 .. length ls - 1] ks ls
      Node s ks os -> Stage (nodeGeo ks os s)
      Points pk ks -> points (not (fixedSpiders o)) pk ks
      Bend b ka kd -> bend b ka kd
      Rebracket g ka kb kc -> Stage (rebracket g ka kb kc)
      Unitor s d ks -> Stage (unitor s d ks)
      UnitEnd -> Stage unitEnd
      UnitStart -> Stage (mirror unitEnd)
      Seq a b -> compose (go b) (go a)
      Beside a b -> tensor (go a) (go b)
      Trace ks d -> Stage (loops (length ks) (toGeo slot (go d)))

-- | The boundary wires that are drawn with the given options.
visible :: Options -> [(String, WireKind)] -> [(String, WireKind)]
visible o ws = [w | w@(_, k) <- ws, explicitCoherence o || k /= UnitWire]

-- * Layout

-- | A point in the plane, @y@ growing downwards.
type Pt = (Double, Double)

-- | The course of a piece of wire.
data Path
  = -- | straight from one point to another
    Line Pt Pt
  | -- | from one point down to another, leaving and arriving vertically
    Curve Pt Pt
  | -- | along the given corners, rounded
    Loop (NonEmpty Pt)
  | -- | a quarter of an ellipse, leaving the first point vertically and reaching the second
    -- horizontally: half of a bend
    Quarter Pt Pt
  deriving (Show)

-- | What a diagram is drawn with.
data Shape
  = -- | a piece of wire of the given kind: plain, dotted for a unit wire, hollow for a dual one
    Piece WireKind Path
  | -- | a box between two corners, with a name
    Box Pt Pt String
  | -- | the dashed frame of an identity, between two corners
    Frame Pt Pt
  | -- | a bracket grouping wires, from one point to another, its ends pointing down or up
    Bracket Pt Pt Bool
  | -- | a point on a wire, filled for a comonoid and hollow for a monoid
    Point Pt Bool
  | -- | the label of the wire leaving a box
    Label Pt String
  | -- | the label of a boundary wire, centred
    Boundary Pt String
  | -- | the equals sign of an equation
    Equals Pt
  deriving (Show)

-- | A shape moved right by @dx@ and down by @dy@.
move :: Double -> Double -> Shape -> Shape
move dx dy = \case
  Piece k (Line a b) -> Piece k (Line (at a) (at b))
  Piece k (Curve a b) -> Piece k (Curve (at a) (at b))
  Piece k (Loop ps) -> Piece k (Loop (fmap at ps))
  Piece k (Quarter a b) -> Piece k (Quarter (at a) (at b))
  Box a b s -> Box (at a) (at b) s
  Frame a b -> Frame (at a) (at b)
  Bracket a b down -> Bracket (at a) (at b) down
  Point a f -> Point (at a) f
  Label a s -> Label (at a) s
  Boundary a s -> Boundary (at a) s
  Equals a -> Equals (at a)
  where
    at (x, y) = (x + dx, y + dy)

-- | Where a wire enters a drawing along its top or leaves it along its bottom: how far along, the
-- kind of wire, and, for a leg of a copy or merge point that may trade places with the point's
-- other leg, which point it is a leg of.
data Port = Port {portX :: Double, portKind :: WireKind, portLegs :: Maybe Int}
  deriving (Show)

port :: Double -> WireKind -> Port
port x k = Port x k Nothing

-- | A port moved right by @dx@.
shiftPort :: Double -> Port -> Port
shiftPort dx p = p{portX = portX p + dx}

-- | A drawn diagram: its size, its input and output ports, and its shapes.
data Geo = Geo
  { geoWidth :: Double
  , geoHeight :: Double
  , geoIns :: [Port]
  , geoOuts :: [Port]
  , geoShapes :: [Shape]
  }
  deriving (Show)

-- | How a diagram is drawn. A diagram that only permutes its wires has no height of its own: its
-- crossings are drawn in the band where the wires next change position, so that a 'swap' next to
-- a box does not make the box taller.
data Layout
  = -- | output @j@ continues input @p !! j@, with the kinds of the inputs and of the outputs
    Wiring [Int] [WireKind] [WireKind]
  | Stage Geo
  deriving (Show)

-- | The distance between neighbouring wires.
slot :: Double
slot = 32

-- | The length of wire above and below a box.
stub :: Double
stub = 10

-- | The height of a box.
boxHeight :: Double
boxHeight = 24

-- | The distance between the rails of neighbouring trace loops.
loopGap :: Double
loopGap = 14

-- | How far the innermost trace loop runs below and above the diagram it loops round, clear of
-- the wire labels.
loopClearance :: Double
loopClearance = 6

-- | The width of a name, roughly, in the box font.
textWidth :: String -> Double
textWidth s = 7.5 * fromIntegral (length s)

-- | The positions of @n@ wires, one slot apart.
slots :: Int -> [Double]
slots n = [slot * (fromIntegral k + 0.5) | k <- [0 .. n - 1]]

width :: Int -> Double
width n = slot * fromIntegral n

-- | Ports at the given positions, for wires of the given kinds.
ports :: [Double] -> [WireKind] -> [Port]
ports = zipWith port

-- | A permutation of wires of the given kinds, drawn over the given height.
wiringGeo :: Double -> [Int] -> [WireKind] -> [WireKind] -> Geo
wiringGeo h p ks os =
  let xs = slots (length p)
  in Geo
       { geoWidth = width (length p)
       , geoHeight = h
       , geoIns = ports xs ks
       , geoOuts = ports xs os
       , geoShapes = [Piece (ks !! i) (Curve (xs !! i, 0) (x, h)) | (x, i) <- zip xs p]
       }

-- | Straight wires of the given kinds at the given positions, from the top down to @h@.
verticals :: Double -> [Double] -> [WireKind] -> [Shape]
verticals h xs ks = [Piece u (Line (x, 0) (x, h)) | (x, u) <- zip xs ks]

-- | A layout as geometry, a permutation drawn over the given height.
toGeo :: Double -> Layout -> Geo
toGeo h (Wiring p ks os) = wiringGeo h p ks os
toGeo _ (Stage g) = g

layoutHeight :: Layout -> Double
layoutHeight Wiring{} = 0
layoutHeight (Stage g) = geoHeight g

-- | Geometry made taller, centred, with its wires extended to the new top and bottom.
stretch :: Double -> Geo -> Geo
stretch h g
  | h <= geoHeight g = g
  | otherwise =
      g
        { geoHeight = h
        , geoShapes =
            map (move 0 pad) (geoShapes g)
              ++ [Piece k (Line (x, 0) (x, pad)) | Port x k _ <- geoIns g]
              ++ [Piece k (Line (x, pad + geoHeight g) (x, h)) | Port x k _ <- geoOuts g]
        }
  where
    pad = (h - geoHeight g) / 2

-- | Two layouts side by side, as tall as the taller one.
tensor :: Layout -> Layout -> Layout
tensor (Wiring p ks os) (Wiring q ls ps) = Wiring (p ++ map (+ length p) q) (ks ++ ls) (os ++ ps)
tensor l r =
  let h = max (layoutHeight l) (layoutHeight r)
      gl = stretch h (toGeo h l)
      gr = stretch h (toGeo h r)
      w = geoWidth gl
      -- the points on the right are numbered after those on the left
      n = 1 + maximum (-1 : [i | Port _ _ (Just i) <- geoIns gl ++ geoOuts gl])
      right q = (shiftPort w q){portLegs = (+ n) <$> portLegs q}
  in Stage
       Geo
         { geoWidth = w + geoWidth gr
         , geoHeight = h
         , geoIns = geoIns gl ++ map right (geoIns gr)
         , geoOuts = geoOuts gl ++ map right (geoOuts gr)
         , geoShapes = geoShapes gl ++ map (move w 0) (geoShapes gr)
         }

-- | The layout of @after . before@. A permutation is absorbed into the layout next to it, so its
-- crossings end up in the next band.
compose :: Layout -> Layout -> Layout
compose (Wiring p _ os) (Wiring q ls _) = Wiring (map (q !!) p) ls os
compose (Stage g) (Wiring p ks _) = Stage g{geoIns = [(geoIns g !! j){portKind = k} | (j, k) <- zip (inverse p) ks]}
compose (Wiring p _ os) (Stage f) = Stage f{geoOuts = [(geoOuts f !! i){portKind = k} | (i, k) <- zip p os]}
compose (Stage g) (Stage f) = Stage (stack f g)

inverse :: [Int] -> [Int]
inverse p = map snd (List.sort (zip p [0 ..]))

-- | @before@ above @after@, with a band of wires between them. The two are placed so that the wires
-- between them move sideways as little as possible.
stack :: Geo -> Geo -> Geo
stack f0 g0 =
  let f = f0{geoOuts = untangle (map portX (geoIns g0)) (geoOuts f0)}
      g = g0{geoIns = untangle (map portX (geoOuts f)) (geoIns g0)}
      dxs = zipWith (\a b -> portX a - portX b) (geoOuts f) (geoIns g)
      off = if null dxs then (geoWidth f - geoWidth g) / 2 else List.sort dxs !! (length dxs `div` 2)
      sf = negate (min 0 off)
      sg = off + sf
      ends = [(portX a + sf, portX b + sg, portKind a) | (a, b) <- zip (geoOuts f) (geoIns g)]
      hb = bandHeight (maximum (0 : [abs (a - b) | (a, b, _) <- ends]))
      hf = geoHeight f
  in Geo
       { geoWidth = max (geoWidth f + sf) (geoWidth g + sg)
       , geoHeight = hf + hb + geoHeight g
       , geoIns = map (shiftPort sf) (geoIns f)
       , geoOuts = map (shiftPort sg) (geoOuts g)
       , geoShapes =
           map (move sf 0) (geoShapes f)
             ++ [Piece u (Curve (a, hf) (b, hf + hb)) | (a, b, u) <- ends]
             ++ map (move sg (hf + hb)) (geoShapes g)
       }

-- | Ports with the legs of each point that may trade places reordered, so that they run to their
-- targets without crossing each other.
untangle :: [Double] -> [Port] -> [Port]
untangle targets ps = [p{portX = fromMaybe (portX p) (lookup i moved)} | (i, p) <- zip [0 ..] ps]
  where
    legs = [(i, l) | (i, Port _ _ (Just l)) <- zip [0 :: Int ..] ps]
    groups = map (map fst . NE.toList) (NE.groupAllWith snd legs)
    moved = concat [zip (List.sortOn (targets !!) grp) (List.sort (map (portX . (ps !!)) grp)) | grp <- groups]

-- | The height of a band whose wires move sideways by at most @d@.
bandHeight :: Double -> Double
bandHeight d
  | d < 0.5 = 0
  | otherwise = max 16 (min 64 (0.6 * d))

-- | A box with inputs of the given kinds, and outputs with the given labels and kinds. Unit wires
-- get no label.
nodeGeo :: [WireKind] -> [(String, WireKind)] -> String -> Geo
nodeGeo inKinds outWires s =
  Geo
    { geoWidth = w
    , geoHeight = h
    , geoIns = ports ins inKinds
    , geoOuts = ports outs (map snd outWires)
    , geoShapes =
        [Piece u (Line (x, 0) (x, stub)) | (x, u) <- zip ins inKinds]
          ++ [Piece u (Line (x, stub + boxHeight) (x, h)) | (x, (_, u)) <- zip outs outWires]
          ++ [Box ((w - bw) / 2, stub) ((w + bw) / 2, stub + boxHeight) s]
          ++ [Label (x + 3, stub + boxHeight + 9) o | (x, (o, ok)) <- zip outs outWires, ok /= UnitWire]
    }
  where
    n = length inKinds
    m = length outWires
    k = max 1 (max n m)
    bw = max (textWidth s + 14) (fromIntegral (k - 1) * slot + 18)
    w = max (bw + 8) (fromIntegral k * slot)
    h = stub + boxHeight + stub
    at c = [w / 2 + (fromIntegral i - fromIntegral (c - 1) / 2) * slot | i <- [0 .. c - 1]]
    ins = at n
    outs = at m

-- | The points of a (co)monoid, one on each wire of the given kinds; nothing drawn when there are
-- no wires. The legs of copy and merge points may trade places when @free@.
points :: Bool -> PointKind -> [WireKind] -> Layout
points _ _ [] = Wiring [] [] []
points free pk ks = Stage $ case pk of
  UnitPoint -> unit
  DiscardPoint -> mirror unit
  MergePoint -> merge
  CopyPoint -> mirror merge
  where
    n = length ks
    xs = slots n
    -- each copy or merge point forks to two slots; the first legs are listed before the second
    -- ones, so with several wires the next band sorts them
    firsts = [slot * (2 * fromIntegral i + 0.5) | i <- [0 .. n - 1]]
    seconds = map (+ slot) firsts
    ps = zipWith (\l r -> (l + r) / 2) firsts seconds
    leg i = if free then Just i else Nothing
    legs = [Port x u (leg i) | (i, x, u) <- zip3 [0 ..] firsts ks] ++ [Port x u (leg i) | (i, x, u) <- zip3 [0 ..] seconds ks]
    -- the wires stop at the edge of a hollow point, so that the background shows through it
    unit =
      Geo (width n) 12 [] (ports xs ks) (concat [[Piece u (Line (x, 7) (x, 12)), Point (x, 4) False] | (x, u) <- zip xs ks])
    merge =
      Geo
        (width (2 * n))
        20
        legs
        (ports ps ks)
        ( concat
            [ [Piece u (Curve (l, 0) (x, 11)), Piece u (Curve (r, 0) (x, 11)), Piece u (Line (x, 17) (x, 20)), Point (x, 14) False]
            | (x, l, r, u) <- List.zip4 ps firsts seconds ks
            ]
        )

-- | The height of a swap drawn on its own.
swapHeight :: Double
swapHeight = 24

-- | A permutation of wires of the given kinds, drawn on its own when @explicit@.
permutation :: Bool -> [WireKind] -> [Int] -> Layout
permutation explicit ks p =
  let os = map (ks !!) p
  in if explicit then Stage (wiringGeo swapHeight p ks os) else Wiring p ks os

-- | The identity on wires of the given kinds, drawn in a dashed frame when @explicit@.
identity :: Bool -> [WireKind] -> Layout
identity explicit ks
  | explicit =
      let n = length ks
          w = if n == 0 then slot / 2 else width n
          h = 18
          xs = slots n
      in Stage
           ( Geo
               w
               h
               (ports xs ks)
               (ports xs ks)
               (verticals h xs ks ++ [Frame (2, 3) (w - 2, h - 3)])
           )
  | otherwise = Wiring [0 .. length ks - 1] ks ks

-- | Bends joining each wire of the given kinds to its dual: for a 'Cup' the wires and then their
-- duals leave along the bottom, for a 'Cap' the duals and then the wires enter along the top.
-- Each bend changes style at its apex.
bend :: BendKind -> [WireKind] -> [WireKind] -> Layout
bend _ [] _ = Wiring [] [] []
bend kind ka kd =
  let m = length ka
      h = 18
      xs = slots (2 * m)
      (lefts, rights) = splitAt m xs
      -- bends with the given kinds on their left and on their right halves, opening downwards
      cups ls rs =
        Geo (width (2 * m)) h [] (ports xs (ls ++ rs)) $
          concat
            [ [Piece k (Quarter (l, h) ((l + r) / 2, 3)), Piece k' (Quarter (r, h) ((l + r) / 2, 3))]
            | (l, r, k, k') <- List.zip4 lefts rights ls rs
            ]
  in Stage $ case kind of
       Cup -> cups ka kd
       Cap -> mirror (cups kd ka)

-- | An associator from the grouping given to the other one, on wires of the given kinds: the
-- wires with a bracket over the pair grouped at the top and one under the pair grouped at the
-- bottom.
rebracket :: Grouping -> [WireKind] -> [WireKind] -> [WireKind] -> Geo
rebracket grouping ka kb kc =
  let ks = ka ++ kb ++ kc
      n = length ks
      h = 30
      xs = slots n
      group from to
        | to <= from = []
        | otherwise = [(xs !! from - slot / 3, xs !! (to - 1) + slot / 3)]
      ab = group 0 (length ka + length kb)
      bc = group (length ka) n
      leftFirst =
        Geo
          (width n)
          h
          (ports xs ks)
          (ports xs ks)
          ( verticals h xs ks
              ++ [Bracket (x0, 6) (x1, 6) True | (x0, x1) <- ab]
              ++ [Bracket (x0, h - 6) (x1, h - 6) False | (x0, x1) <- bc]
          )
  in case grouping of LeftFirst -> leftFirst; RightFirst -> mirror leftFirst

-- | A unitor on wires of the given kinds: a dotted unit wire that runs into the outermost wire on
-- its side or out of it.
unitor :: Side -> Direction -> [WireKind] -> Geo
unitor side dir ks =
  let n = length ks
      h = 16
      xs = case side of OnLeft -> map (+ slot) (slots n); OnRight -> slots n
      xu = case side of OnLeft -> slot / 2; OnRight -> slot * (fromIntegral n + 0.5)
      other = case side of OnLeft -> take 1 xs; OnRight -> drop (n - 1) xs
      place :: forall t. t -> [t] -> [t]
      place u us = case side of OnLeft -> u : us; OnRight -> us ++ [u]
      joining = case other of
        [x] -> Curve (xu, 0) (x, h)
        _ -> Line (xu, 0) (xu, h / 2)
      absorb =
        Geo
          (width (n + 1))
          h
          (ports (place xu xs) (place UnitWire ks))
          (ports xs ks)
          (Piece UnitWire joining : verticals h xs ks)
  in case dir of Absorb -> absorb; Create -> mirror absorb

-- | The end of a unit wire.
unitEnd :: Geo
unitEnd = Geo slot 8 [port (slot / 2) UnitWire] [] [Piece UnitWire (Line (slot / 2, 0) (slot / 2, 8))]

-- | Geometry upside down: its inputs become its outputs and the other way round, so that a merge
-- point becomes a copy point, a cup a cap, and so on. A point is filled when it was hollow and
-- hollow when it was filled, as the points of a comonoid are the mirror images of a monoid's. A
-- piece of wire still runs from top to bottom, except a bend's, which runs towards its apex.
mirror :: Geo -> Geo
mirror g = g{geoIns = geoOuts g, geoOuts = geoIns g, geoShapes = map flipShape (geoShapes g)}
  where
    h = geoHeight g
    f (x, y) = (x, h - y)
    corners (x0, y0) (x1, y1) = ((x0, h - y1), (x1, h - y0))
    flipShape = \case
      Piece k (Line a b) -> Piece k (Line (f b) (f a))
      Piece k (Curve a b) -> Piece k (Curve (f b) (f a))
      Piece k (Loop ps) -> Piece k (Loop (NE.reverse (fmap f ps)))
      Piece k (Quarter a b) -> Piece k (Quarter (f a) (f b))
      Box a b s -> uncurry Box (corners a b) s
      Frame a b -> uncurry Frame (corners a b)
      Bracket a b down -> Bracket (f a) (f b) (not down)
      Point a filled -> Point (f a) (not filled)
      Label a s -> Label (f a) s
      Boundary a s -> Boundary (f a) s
      Equals a -> Equals (f a)

-- | The first @k@ wires fed back from the outputs to the inputs, each looping round the side where
-- it crosses fewer other wires. The loops on one side are nested: the one whose ends are nearest
-- that side runs innermost.
loops :: Int -> Geo -> Geo
loops k g =
  Geo
    { geoWidth = left + w + right
    , geoHeight = depth + h + depth
    , geoIns = map (shiftPort left) (drop k (geoIns g))
    , geoOuts = map (shiftPort left) (drop k (geoOuts g))
    , geoShapes =
        map (move left depth) (geoShapes g)
          ++ [Piece u (Line (x + left, 0) (x + left, depth)) | Port x u _ <- drop k (geoIns g)]
          ++ [Piece u (Line (x + left, depth + h) (x + left, depth + h + depth)) | Port x u _ <- drop k (geoOuts g)]
          ++ zipWith (loop 0 (\d -> left - d)) [1 ..] (List.sortOn (\(a, b, _) -> min a b) lefts)
          ++ zipWith (loop (loopGap / 2) (\d -> left + w + d)) [1 ..] (List.sortOn (\(a, b, _) -> negate (max a b)) rights)
    }
  where
    w = geoWidth g
    h = geoHeight g
    (lefts, rights) = List.partition goesLeft [(portX a, portX b, portKind a) | (a, b) <- take k (zip (geoIns g) (geoOuts g))]
    -- a loop goes round the side where it crosses fewer of the wires that carry on, and round the
    -- side its ends are nearest to when that is a tie
    carryOn = map portX (drop k (geoIns g) ++ drop k (geoOuts g))
    goesLeft (a, b, _) =
      let crossLeft = length (filter (< min a b) carryOn)
          crossRight = length (filter (> max a b) carryOn)
      in crossLeft < crossRight || (crossLeft == crossRight && a + b <= w)
    left = loopGap * fromIntegral (length lefts)
    right = loopGap * fromIntegral (length rights)
    depth = loopClearance + loopGap * fromIntegral (max (length lefts) (length rights))
    -- the loops on the right run half a gap higher than those on the left, so that a left and a
    -- right loop cross instead of running along each other
    loop :: Double -> (Double -> Double) -> Int -> (Double, Double, WireKind) -> Shape
    loop lift rail level (xi, xo, u) =
      let d = loopGap * fromIntegral level
          v = loopClearance + d - lift
          x = rail d
      in Piece u $
           Loop
             ( (xo + left, depth + h)
                 :| [ (xo + left, depth + h + v)
                    , (x, depth + h + v)
                    , (x, depth - v)
                    , (xi + left, depth - v)
                    , (xi + left, depth)
                    ]
             )

-- * Rendering

-- | The height of the row of boundary labels.
labelRow :: Double
labelRow = 16

-- | Geometry with its boundary: the input labels above and the output labels below, each joined
-- to its wire by a band @top@ and @bottom@ tall. Legs that may trade places are put in the
-- boundary's order.
framed :: Double -> Double -> [(String, WireKind)] -> [(String, WireKind)] -> Geo -> Geo
framed top bottom ins outs g =
  Geo
    { geoWidth = geoWidth g
    , geoHeight = labelRow + top + geoHeight g + bottom + labelRow
    , geoIns = []
    , geoOuts = []
    , geoShapes =
        [Boundary (x, labelRow - 4) s | (x, (s, _)) <- zip inXs ins]
          ++ [Piece u (Curve (x, labelRow) (y, labelRow + top)) | (x, y, (_, u)) <- zip3 inXs inYs ins]
          ++ map (move 0 (labelRow + top)) (geoShapes g)
          ++ [Piece u (Curve (y, bottomAt) (x, bottomAt + bottom)) | (x, y, (_, u)) <- zip3 outXs outYs outs]
          ++ [Boundary (x, bottomAt + bottom + labelRow - 3) s | (x, (s, _)) <- zip outXs outs]
    }
  where
    inYs = inOrder (geoIns g)
    outYs = inOrder (geoOuts g)
    inXs = List.sort inYs
    outXs = List.sort outYs
    bottomAt = labelRow + top + geoHeight g

-- | The positions of ports, the legs of each point that may trade places put in the order of the
-- wires.
inOrder :: [Port] -> [Double]
inOrder ps = map portX (untangle (map fromIntegral [0 .. length ps - 1]) ps)

-- | The height of the bands joining the boundary to the wires.
boundaryBands :: Geo -> (Double, Double)
boundaryBands g =
  let band xs = max 8 (bandHeight (maximum (0 : zipWith (\a b -> abs (a - b)) (List.sort xs) xs)))
  in (band (inOrder (geoIns g)), band (inOrder (geoOuts g)))

-- | The diagram as an SVG document, with the 'defaultOptions'.
render :: forall (as :: [W]) (bs :: [W]). Svg (S as) (S bs) -> String
render = renderWith defaultOptions

-- | The diagram as an SVG document.
renderWith :: forall (as :: [W]) (bs :: [W]). Options -> Svg (S as) (S bs) -> String
renderWith o (Svg _ d) = sideBySide @as @bs o [d]

-- | Two parallel diagrams side by side, with an equals sign between them, with the
-- 'defaultOptions'.
renderEquation :: forall (as :: [W]) (bs :: [W]). Svg (S as) (S bs) -> Svg (S as) (S bs) -> String
renderEquation = renderEquationWith defaultOptions

-- | Two parallel diagrams side by side, with an equals sign between them. Neither is simplified:
-- the picture shows two different diagrams that mean the same.
renderEquationWith
  :: forall (as :: [W]) (bs :: [W]). Options -> Svg (S as) (S bs) -> Svg (S as) (S bs) -> String
renderEquationWith o (Svg _ l) (Svg _ r) = sideBySide @as @bs o [l, r]

-- | Diagrams from the wires @as@ to the wires @bs@ as one SVG document: side by side, each with
-- the boundary labels, stretched to the height of the tallest, and with an equals sign between
-- each and the next.
sideBySide :: forall (as :: [W]) (bs :: [W]). (IsList as, IsList bs) => Options -> [Diagram] -> String
sideBySide o ds =
  let ls = map (layout o) ds
      h = maximum (0 : map layoutHeight ls)
      gs = [stretch h (toGeo (max h slot) l) | l <- ls]
      bands = map boundaryBands gs
      side = framed (maximum (0 : map fst bands)) (maximum (0 : map snd bands)) (visible o (wires @as)) (visible o (wires @bs))
      fs = map side gs
      -- each side starts where the one before it ends, with room for the equals sign between
      offsets = scanl (\x f -> x + geoWidth f + 48) 0 fs
      equalsAt = case fs of f : _ -> geoHeight f / 2; [] -> 0
      placed i x f = [Equals (x - 24, equalsAt) | i > (0 :: Int)] ++ map (move x 0) (geoShapes f)
  in document
       Geo
         { geoWidth = last offsets - 48
         , geoHeight = maximum (0 : map geoHeight fs)
         , geoIns = []
         , geoOuts = []
         , geoShapes = concat (zipWith3 placed [0 ..] offsets fs)
         }

-- | The laws of @cs@ drawn with the 'defaultOptions', see 'lawSvgsWith'.
lawSvgs :: forall (cs :: [Kind -> Constraint]). (Laws cs, All cs SVG) => [(String, String)]
lawSvgs = lawSvgsWith @cs defaultOptions

-- | The laws of @cs@, each drawn as an equation by 'renderEquationWith', with its name. The object
-- variables are single wires @'Wire' "a"@ to @'Wire' "e"@, and the arrows a law asks for are 'node's with the names
-- it gives them.
lawSvgsWith :: forall (cs :: [Kind -> Constraint]). (Laws cs, All cs SVG) => Options -> [(String, String)]
lawSvgsWith o = [(lawName law, draw law) | law <- laws @cs]
  where
    draw :: Law cs -> String
    draw (Law _ body) = case runIdentity (body @(S '[Wire "a"]) @(S '[Wire "b"]) @(S '[Wire "c"]) @(S '[Wire "d"]) @(S '[Wire "e"]) box) of
      l@Svg{} :=: r -> renderEquationWith o l r
    box :: forall (x :: SVG) (y :: SVG). (Ob x, Ob y) => String -> Identity (x ~> y)
    box s = Identity (node @(UN S x) @(UN S y) s)

-- | An SVG document showing the geometry. Wires, outlines and text use the current colour. Boxes
-- are not filled, and the wires stop at the edge of a hollow point, so the background shows
-- through both. Only the core of a dual wire is painted, in @--sd-paper@ (white when it is not
-- set), which a page can set to its background.
document :: Geo -> String
document g =
  "<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"sd\" viewBox=\""
    ++ unwords (map num [-margin, -margin, geoWidth g + 2 * margin, geoHeight g + 2 * margin])
    ++ "\" width=\""
    ++ num (geoWidth g + 2 * margin)
    ++ "\" height=\""
    ++ num (geoHeight g + 2 * margin)
    ++ "\"><style>"
    ++ ".sd path{fill:none;stroke:currentColor;stroke-width:1.3;stroke-linecap:round}"
    ++ ".sd .u path{stroke-dasharray:1.3 2.6}"
    ++ ".sd .d path{stroke-linecap:butt;stroke-width:4}"
    ++ ".sd .di path{stroke:var(--sd-paper,#fff);stroke-width:1.6}"
    ++ ".sd rect,.sd .h{fill:none;stroke:currentColor;stroke-width:1.3}"
    ++ ".sd .f{fill:currentColor}"
    ++ ".sd .id{stroke-width:0.8;stroke-dasharray:3 2}"
    ++ ".sd .br{stroke-width:0.9}"
    ++ ".sd text{fill:currentColor;font-family:'STIX Two Text','Times New Roman',serif;font-style:italic}"
    ++ ".sd .n{font-size:15px;text-anchor:middle;dominant-baseline:central}"
    ++ ".sd .l{font-size:11px}"
    ++ ".sd .b{font-size:13px;text-anchor:middle}"
    ++ ".sd .e{font-size:22px;font-style:normal;text-anchor:middle;dominant-baseline:central}"
    ++ "</style>"
    -- the outlines of all dual wires go below all their cores, so that where two dual wires meet or
    -- cross the cores run on unbroken
    ++ group "d" duals
    ++ group "di" duals
    ++ concatMap path (chains Plain)
    ++ group "u" (chains UnitWire)
    ++ concat [shape x | x <- geoShapes g, not (isPiece x), not (isText x)]
    ++ concat [shape x | x <- geoShapes g, isText x]
    ++ "</svg>"
  where
    margin = 8
    -- the pieces of wire of one kind, joined into as few paths as possible, so that no seams show
    duals = chains DualWire
    chains k = joined [segment p | Piece k' p <- geoShapes g, k' == k]
    group _ [] = ""
    group cls ds = "<g class=\"" ++ cls ++ "\">" ++ concatMap path ds ++ "</g>"
    isPiece = \case Piece{} -> True; _ -> False
    isText = \case Label{} -> True; Boundary{} -> True; Equals{} -> True; _ -> False

-- | Where a piece of wire starts and ends, and the SVG path from its start.
segment :: Path -> (Pt, Pt, String)
segment = \case
  Line a b -> (a, b, "L" ++ pt b)
  Curve a@(ax, ay) b@(bx, by)
    | abs (ax - bx) < 0.5 -> (a, b, "L" ++ pt b)
    | otherwise -> let my = (ay + by) / 2 in (a, b, "C" ++ pt (ax, my) ++ " " ++ pt (bx, my) ++ " " ++ pt b)
  Loop ps -> (NE.head ps, NE.last ps, rounded ps)
  Quarter a@(ax, ay) b@(bx, by) ->
    (a, b, "C" ++ pt (ax, ay + (by - ay) * kappa) ++ " " ++ pt (bx - (bx - ax) * kappa, by) ++ " " ++ pt b)

-- | Pieces of wire joined where one ends where the next starts, each chain as one path. A chain
-- starts at a piece that no other piece leads into.
joined :: [(Pt, Pt, String)] -> [String]
joined [] = []
joined ps@(p : _) =
  let start = fromMaybe p (List.find (\(a, _, _) -> key a `notElem` [key b | (_, b, _) <- ps]) ps)
      chain = follow start (List.delete start ps)
      rest = foldr List.delete ps (start : chain)
      (a0, _, _) = start
  in ("M" ++ pt a0 ++ concat [d | (_, _, d) <- start : chain]) : joined rest
  where
    key (x, y) = (round (x * 100), round (y * 100)) :: (Int, Int)
    follow (_, b, _) qs = case List.find (\(a', _, _) -> key a' == key b) qs of
      Just next -> next : follow next (List.delete next qs)
      Nothing -> []

path :: String -> String
path d = "<path d=\"" ++ d ++ "\"/>"

-- | One shape as SVG.
shape :: Shape -> String
shape = \case
  Box a@(x0, y0) b@(x1, y1) s -> rect "" 7 a b ++ text "n" ((x0 + x1) / 2, (y0 + y1) / 2) s
  Frame a b -> rect " class=\"id\"" 4 a b
  Bracket (x0, y0) (x1, y1) down ->
    let tick = if down then 4 else -4
    in "<path class=\"br\" d=\"M"
         ++ pt (x0, y0 + tick)
         ++ "L"
         ++ pt (x0, y0)
         ++ "L"
         ++ pt (x1, y1)
         ++ "L"
         ++ pt (x1, y1 + tick)
         ++ "\"/>"
  Point (x, y) filled -> "<circle cx=\"" ++ num x ++ "\" cy=\"" ++ num y ++ "\" r=\"3\" class=\"" ++ (if filled then "f" else "h") ++ "\"/>"
  Label p s -> text "l" p s
  Boundary p s -> text "b" p s
  Equals p -> text "e" p "="
  -- wires are drawn by 'document', joined into as few paths as possible
  Piece{} -> ""
  where
    rect cls r (x0, y0) (x1, y1) =
      "<rect"
        ++ cls
        ++ " x=\""
        ++ num x0
        ++ "\" y=\""
        ++ num y0
        ++ "\" width=\""
        ++ num (x1 - x0)
        ++ "\" height=\""
        ++ num (y1 - y0)
        ++ "\" rx=\""
        ++ num r
        ++ "\"/>"
    text cls (x, y) s = "<text class=\"" ++ cls ++ "\" x=\"" ++ num x ++ "\" y=\"" ++ num y ++ "\">" ++ Dot.htmlEscape s ++ "</text>"

-- | How far along its tangent a cubic curve's control point lies, as a fraction of the radius,
-- for the curve to be a quarter circle.
kappa :: Double
kappa = 0.5523

-- | The radius of a bend, and of the corners of a trace loop, so that a small loop is a cup and a
-- cap joined by straight wire.
bendRadius :: Double
bendRadius = slot / 2

-- | A path from the first of the given corners along the rest, each corner rounded with a quarter
-- circle of radius 'bendRadius', or less where the wire on either side of it is too short. A
-- stretch of wire between two corners is shared between them; one at either end belongs to its
-- corner alone.
rounded :: NonEmpty Pt -> String
rounded ne = concatMap corner (zip3 [0 :: Int ..] ps (drop 1 ps `zip` drop 2 ps)) ++ "L" ++ pt (NE.last ne)
  where
    ps = NE.toList ne
    lastCorner = length ps - 3
    corner (i, prev, (c, next)) =
      let room end q = if end then dist c q else dist c q / 2
          rr = minimum [bendRadius, room (i == 0) prev, room (i == lastCorner) next]
          a = towards c prev rr
          b = towards c next rr
      in "L" ++ pt a ++ "C" ++ pt (between a c) ++ " " ++ pt (between b c) ++ " " ++ pt b
    dist (x0, y0) (x1, y1) = sqrt ((x1 - x0) ^ (2 :: Int) + (y1 - y0) ^ (2 :: Int))
    towards c@(cx, cy) q@(x, y) d = let t = d / dist c q in (cx + (x - cx) * t, cy + (y - cy) * t)
    -- the control point of a quarter circle, from its end towards the corner
    between (x, y) (cx, cy) = (x + (cx - x) * kappa, y + (cy - y) * kappa)

pt :: Pt -> String
pt (x, y) = num x ++ " " ++ num y

num :: Double -> String
num x = showFFloat (Just 1) x ""
