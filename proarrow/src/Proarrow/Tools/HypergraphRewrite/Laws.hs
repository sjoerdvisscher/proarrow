{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Instantiate named categorical laws as hypergraph rewrite rules.
module Proarrow.Tools.HypergraphRewrite.Laws
  ( Direction (..)
  , ruleWith
  , ruleWithDirection
  , parameterRuleWith
  , parameterRuleWithDirection
  , parameterRulesWith
  , subgraphRuleWithDirection
  , rewritesWith
  , rewritesWithDirection
  ) where

import Data.Typeable (Typeable)
import Prelude

import Proarrow.Category.Instance.OpenHypergraph (OPENHG, WireSorts, Wires)
import Proarrow.Core (CategoryOf (..))
import Proarrow.Optic.Iso (DecidableIso)
import Proarrow.Tools.HypergraphRewrite (Parameter (..), Rule, parameterRule, rewrites, rule, subgraphRule)
import Proarrow.Tools.Laws (Equation, Law (..), LawBody, Laws (..), lawName, withSides)

-- | Orient an equation as written in its 'Law' body, or in reverse.
data Direction = LeftToRight | RightToLeft
  deriving (Eq, Show)

-- | Select a law left-to-right, using an explicit interpretation to choose its
-- object variables, supplied arrows, and representation of the structures.
-- Unknown and ambiguous law names are errors. The interpreted equation must
-- satisfy 'rule'\'s restriction on the oriented left boundary.
--
-- The interpretation receives the polymorphic body. Instantiate it in a
-- diagram category supporting the requested structures, then use 'withSides'
-- to lower both sides to parallel open hypergraphs. Supplied arrows are concrete;
-- this does not introduce variables matching arbitrary subdiagrams.
ruleWith
  :: forall cs s l
   . (Laws cs)
  => String
  -> (LawBody cs -> Equation (OPENHG s l))
  -> Either String (Rule s l)
ruleWith name = ruleWithDirection @cs name LeftToRight

-- | Like 'ruleWith', with an explicit choice of direction.
ruleWithDirection
  :: forall cs s l
   . (Laws cs)
  => String
  -> Direction
  -> (LawBody cs -> Equation (OPENHG s l))
  -> Either String (Rule s l)
ruleWithDirection name direction interpret = do
  equation <- interpretLaw @cs name interpret
  withSides equation $ \lhs rhs -> case direction of
    LeftToRight -> rule lhs rhs
    RightToLeft -> rule rhs lhs

-- | Select a law left-to-right with the label parameters of 'parameterRule'.
-- The interpretation supplies named arrows as boxes labelled with 'Variable',
-- and structural operations as fixed constructors or 'Literal' fields.
-- Repeated names must bind equal values; the right side reuses those bindings.
-- Object choices and box arities remain fixed, and variables do not match subdiagrams.
-- Compile once, then apply with 'rewrites' or include in 'Proarrow.Tools.HypergraphRewrite.compileRules'.
parameterRuleWith
  :: forall cs s f a
   . (Laws cs, Traversable f, Eq (f ()), Typeable f, Eq a)
  => String
  -> (LawBody cs -> Equation (OPENHG s (f (Parameter a))))
  -> Either String (Rule s (f a))
parameterRuleWith name = parameterRuleWithDirection @cs name LeftToRight

-- | Like 'parameterRuleWith', with an explicit choice of direction.
-- Parameters on the oriented right side must be bound on the oriented left side.
parameterRuleWithDirection
  :: forall cs s f a
   . (Laws cs, Traversable f, Eq (f ()), Typeable f, Eq a)
  => String
  -> Direction
  -> (LawBody cs -> Equation (OPENHG s (f (Parameter a))))
  -> Either String (Rule s (f a))
parameterRuleWithDirection name direction interpret = do
  equation <- interpretLaw @cs name interpret
  withSides equation $ \lhs rhs -> case direction of
    LeftToRight -> parameterRule lhs rhs
    RightToLeft -> parameterRule rhs lhs

-- | Instantiate every law left-to-right with 'parameterRuleWith', retaining its
-- name for 'Proarrow.Tools.HypergraphRewrite.compileRules'. Duplicate law names and invalid rules are errors.
parameterRulesWith
  :: forall cs s f a
   . (Laws cs, Traversable f, Eq (f ()), Typeable f, Eq a)
  => (LawBody cs -> Equation (OPENHG s (f (Parameter a))))
  -> Either String [(String, Rule s (f a))]
parameterRulesWith interpret = traverse instantiate (laws @cs)
  where
    instantiate law = do
      let name = lawName law
      r <- parameterRuleWith @cs name interpret
      pure (name, r)

interpretLaw
  :: forall cs k
   . (Laws cs)
  => String -> (LawBody cs -> Equation k) -> Either String (Equation k)
interpretLaw name interpret = case filter ((== name) . lawName) (laws @cs) of
  [] -> Left ("ruleWith: unknown law " ++ show name)
  [Law _ body] -> Right (interpret (\ @a @b @c @d @e mor -> body @a @b @c @d @e mor))
  _ -> Left ("ruleWith: ambiguous law " ++ show name)

-- | Select an explicitly instantiated law left-to-right and enumerate its single-step rewrites.
-- Compile once with 'ruleWith' when applying the same instantiation to several hosts.
rewritesWith
  :: forall cs s l a b
   . (Laws cs, Eq l, DecidableIso s)
  => String
  -> (LawBody cs -> Equation (OPENHG s l))
  -> (a :: OPENHG s l) ~> b
  -> Either String [Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l)]
rewritesWith name = rewritesWithDirection @cs name LeftToRight

-- | Like 'rewritesWith', with an explicit choice of direction.
rewritesWithDirection
  :: forall cs s l a b
   . (Laws cs, Eq l, DecidableIso s)
  => String
  -> Direction
  -> (LawBody cs -> Equation (OPENHG s l))
  -> (a :: OPENHG s l) ~> b
  -> Either String [Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l)]
rewritesWithDirection name direction interpret host =
  fmap (`rewrites` host) (ruleWithDirection @cs name direction interpret)

-- | Select a law with the whole-arrow parameters of 'subgraphRule'.
subgraphRuleWithDirection
  :: forall cs s p l
   . (Laws cs)
  => String
  -> Direction
  -> (p -> Either l String)
  -> (LawBody cs -> Equation (OPENHG s p))
  -> Either String (Rule s l)
subgraphRuleWithDirection name direction classify interpret = do
  equation <- interpretLaw @cs name interpret
  withSides equation $ \lhs rhs -> case direction of
    LeftToRight -> subgraphRule classify lhs rhs
    RightToLeft -> subgraphRule classify rhs lhs
