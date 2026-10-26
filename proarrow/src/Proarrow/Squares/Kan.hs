{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Kan extensions and lifts as squares. Pointwise constructions have only
-- horizontal functor wires; corepresentable encodings use 'CorepStar'. Their
-- pointwiseness is supplied by the underlying profunctor universal properties.
module Proarrow.Squares.Kan where

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (Profunctor, Promonad (..), (//), (:~>))
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Ran qualified as R
import Proarrow.Profunctor.Instance.Rift qualified as L
import Proarrow.Profunctor.Representable (CorepStar (..), Representable (..), mapCorepStar)
import Proarrow.Squares (Sq (..), fromBottom, mapSq, (===))

-- | Evaluate a profunctor right Kan extension. All three wires are vertical.
--
-- > K---r---j---I
-- > |   \   /   |
-- > |     @     |
-- > |     |     |
-- > K-----p-----I
ran :: (Profunctor j, Profunctor p) => Sq (j ::: j R.|> p ::: Nil) (p ::: Nil) Nil Nil
ran = Sq (unProf R.runRanProf)

-- | Factor a square through the right Kan extension.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > K-------g-----------A
-- > |       |           |
-- > |   K...+...j...I   |
-- > |   :   \   /   :   |
-- > |   :     @     :   |
-- > |   :     |     :   |
-- > |   K.....p.....I   |
-- > |                   |
-- > K---------r---------A
--
-- Here @r = j |> p@.
ranUniv
  :: (Profunctor j, Profunctor p, Profunctor g)
  => Sq (j ::: g ::: Nil) (p ::: Nil) Nil Nil
  -> Sq (g ::: Nil) (j R.|> p ::: Nil) Nil Nil
ranUniv = mapSq R.ranUniv

-- | Evaluate a profunctor right Kan lift.
--
-- > I---j---r---K
-- > |   \   /   |
-- > |     @     |
-- > |     |     |
-- > I-----p-----K
rift :: (Profunctor j, Profunctor p) => Sq (p L.<| j ::: j ::: Nil) (p ::: Nil) Nil Nil
rift = Sq (unProf L.runRiftProf)

-- | Factor a square through the right Kan lift.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > A-----------g-------K
-- > |           |       |
-- > |   I...j...+...K   |
-- > |   :   \   /   :   |
-- > |   :     @     :   |
-- > |   :     |     :   |
-- > |   I.....p.....K   |
-- > |                   |
-- > A---------r---------K
--
-- Here @r = p <| j@.
riftUniv
  :: (Profunctor j, Profunctor p, Profunctor g)
  => Sq (g ::: j ::: Nil) (p ::: Nil) Nil Nil
  -> Sq (g ::: Nil) (p L.<| j ::: Nil) Nil Nil
riftUniv = mapSq L.riftUniv

-- | Pointwise Ran: @r . j => p@, with all three functors horizontal.
--
-- > I-----------I
-- > j>---\      |
-- > |     @---->p
-- > r>---/      |
-- > K-----------K
pwRan :: (R.PointwiseRightKanExtension j p) => Sq Nil Nil (j ::: j R.|> p ::: Nil) (p ::: Nil)
pwRan = Sq (unProf R.runRanProf)

-- | The universal property of pointwise Ran.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > A-------------------A
-- > |                   |
-- > |   I...........I   |
-- > |   j>---\      :   |
-- > |   :     @---->p   r
-- > g>-------/      :   |
-- > |   K...........K   |
-- > |                   |
-- > K-------------------K
--
-- Here @r = j |> p@.
pwRanUniv
  :: (R.PointwiseRightKanExtension j p, Representable g)
  => Sq Nil Nil (j ::: g ::: Nil) (p ::: Nil)
  -> Sq Nil Nil (g ::: Nil) (j R.|> p ::: Nil)
pwRanUniv = mapSq R.ranUniv

-- | Pointwise Rift: @j . r => p@, with all three functors horizontal.
--
-- > J-----------J
-- > r>---\      |
-- > |     @---->p
-- > j>---/      |
-- > I-----------I
pwRift :: (L.PointwiseRightKanLift j p) => Sq Nil Nil (p L.<| j ::: j ::: Nil) (p ::: Nil)
pwRift = Sq (unProf L.runRiftProf)

-- | The universal property of pointwise Rift.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > J-------------------J
-- > |                   |
-- > |   J...........J   |
-- > g>-------\      :   |
-- > |   :     @---->p   r
-- > |   j>---/      :   |
-- > |   I...........I   |
-- > |                   |
-- > K-------------------K
--
-- Here @r = p <| j@.
pwRiftUniv
  :: (L.PointwiseRightKanLift j p, Representable g)
  => Sq Nil Nil (g ::: j ::: Nil) (p ::: Nil)
  -> Sq Nil Nil (g ::: Nil) (p L.<| j ::: Nil)
pwRiftUniv = mapSq L.riftUniv

-- | Mate a transformation between corepresentable diagrams into a square.
-- Used for weighted colimits and for mating pointwise Lan and Lift.
corepSquare
  :: (Profunctor j, Corepresentable p, Corepresentable d)
  => (j :.: p :~> d)
  -> Sq (j ::: Nil) Nil (CorepStar d ::: Nil) (CorepStar p ::: Nil)
corepSquare n = Sq (\(CorepStar f :.: j) -> j // CorepStar (coindex (n (j :.: corepUniv)) . f))

-- | Recover the transformation from its corepresentable mate.
corepSquareInv
  :: forall j p d
   . (Profunctor j, Corepresentable p, Corepresentable d)
  => Sq (j ::: Nil) Nil (CorepStar d ::: Nil) (CorepStar p ::: Nil)
  -> j :.: p :~> d
corepSquareInv (Sq n) = unProf (corepMateInv (Prof n))

-- | Undo the corepresentable mate of @j :.: p ~> d@. The weight @j@ may be
-- an arbitrary profunctor, as in a weighted colimit.
corepMateInv
  :: forall j p d
   . (Profunctor j, Corepresentable p, Corepresentable d)
  => Prof (CorepStar d :.: j) (CorepStar p)
  -> Prof (j :.: p) d
corepMateInv (Prof n) = Prof (\(j :.: p) -> j // cotabulate (coindex p . index (n (repUniv :.: j))))

-- | Recover a transformation between corepresentable profunctors from its
-- mate between horizontal functor paths. Mating reverses composition order.
corepComposeSquareInv
  :: forall p q d
   . (Corepresentable p, Corepresentable q, Corepresentable d)
  => Sq Nil Nil (CorepStar d ::: Nil) (CorepStar p ::: CorepStar q ::: Nil)
  -> p :.: q :~> d
corepComposeSquareInv (Sq n) = unProf (corepComposeMateInv (Prof n))

-- | Undo mating between corepresentable composites and their representing
-- functors. The order of composition is reversed.
corepComposeMateInv
  :: forall p q d
   . (Corepresentable p, Corepresentable q, Corepresentable d)
  => Prof (CorepStar d) (CorepStar q :.: CorepStar p)
  -> Prof (p :.: q) d
corepComposeMateInv (Prof n) = Prof \(pq :: (p :.: q) a b) ->
  pq // cotabulate (coindex pq . index (n (repUniv @(CorepStar d) @a)))

-- | Pointwise Lan: @p => l . j@, with all three functors horizontal.
--
-- > I-----------I
-- > |      /--->j
-- > p>----@     |
-- > |      \--->l
-- > K-----------K
pwLan
  :: (L.PointwiseLeftKanExtension j p)
  => Sq Nil Nil (CorepStar p ::: Nil) (CorepStar j ::: CorepStar (p L.<| j) ::: Nil)
pwLan = fromBottom === corepSquare (unProf L.runRiftProf)

-- | The universal property of pointwise Lan. Mating reverses the
-- transformation between the corepresentable profunctors.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > A-------------------A
-- > |                   |
-- > |   I...........I   |
-- > |   :      /--->j   |
-- > l   p>----@     :   |
-- > |   :      \------->g
-- > |   K...........K   |
-- > |                   |
-- > K-------------------K
--
-- Here @l@ is the corepresenting functor of @p <| j@.
pwLanUniv
  :: (L.PointwiseLeftKanExtension j p, Corepresentable g)
  => Sq Nil Nil (CorepStar p ::: Nil) (CorepStar j ::: CorepStar g ::: Nil)
  -> Sq Nil Nil (CorepStar (p L.<| j) ::: Nil) (CorepStar g ::: Nil)
pwLanUniv = mapSq (mapCorepStar . L.riftUniv . corepComposeMateInv)

-- | Pointwise Lift: @p => j . l@, with all three functors horizontal.
--
-- > K-----------K
-- > |      /--->l
-- > p>----@     |
-- > |      \--->j
-- > I-----------I
pwLift
  :: (R.PointwiseLeftKanLift j p)
  => Sq Nil Nil (CorepStar p ::: Nil) (CorepStar (j R.|> p) ::: CorepStar j ::: Nil)
pwLift = fromBottom === corepSquare (unProf R.runRanProf)

-- | The universal property of pointwise Lift.
--
-- The dotted inner square is the input; the solid outer square is the result.
--
-- > K-------------------K
-- > |                   |
-- > |   K...........K   |
-- > |   :      /------->g
-- > l   p>----@     :   |
-- > |   :      \--->j   |
-- > |   I...........I   |
-- > |                   |
-- > J-------------------J
--
-- Here @l@ is the corepresenting functor of @j |> p@.
pwLiftUniv
  :: (R.PointwiseLeftKanLift j p, Corepresentable g)
  => Sq Nil Nil (CorepStar p ::: Nil) (CorepStar g ::: CorepStar j ::: Nil)
  -> Sq Nil Nil (CorepStar (j R.|> p) ::: Nil) (CorepStar g ::: Nil)
pwLiftUniv = mapSq (mapCorepStar . R.ranUniv . corepComposeMateInv)
