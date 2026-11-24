{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Compile free syntax into typed hypergraphs. Each structure box connects its
-- outer endpoints to the endpoints of its immediate children. Composition shares
-- nodes, and identity is a wire. No interpretation of the structures in the
-- hypergraph category is required. A structure box's inputs are its outer input
-- followed by its child outputs; its outputs are its outer output followed by
-- its child inputs. These connections keep child boundaries distinct from the
-- surrounding composition and expose the children to matching.
--
-- 'freeLawRules' compiles laws with object variables and whole-arrow parameters.
-- Object matching uses the reflected free-object grammar, so variables can bind
-- compound objects without adding graph-specific instances of the structures.
module Proarrow.Tools.HypergraphRewrite.Free
  ( NamedArrows (..)
  , Struct (NamedArrow)
  , FREE_OB
  , FreeWire
  , StructureBox
  , fromFreeWith
  , freeLawRule
  , freeLawRuleWithDirection
  , freeLawRules
  ) where

import Control.Monad (foldM, unless)
import Control.Monad.Trans.State.Strict (State, get, put, runState)
import Data.Functor.Identity (Identity (..))
import Data.Kind (Constraint, Type)
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy)
import Data.Type.Equality ((:~:) (..), (:~~:) (..))
import GHC.TypeLits (Symbol)
import Type.Reflection
  ( SomeTypeRep (..)
  , TypeRep
  , Typeable
  , eqTypeRep
  , typeRep
  , typeRepKind
  , typeRepTyCon
  , withTypeable
  , pattern App
  , pattern Con'
  , pattern Fun
  )
import Type.Reflection.Unsafe (mkTrCon)
import Prelude hiding (id, (.))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Discrete)
import Proarrow.Category.Instance.Free
  ( All
  , Elem (..)
  , Embed
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , StructureChild (..)
  , fromAll
  , sameElem
  , structureChildren
  , withLowerOb
  )
import Proarrow.Category.Instance.OpenHypergraph (Box (..), OPENHG, SomeSort, Wires, unsafeOpenHypergraph)
import Proarrow.Category.Instance.Sub (SUBCAT (..))
import Proarrow.Core (Any, CAT, CategoryOf (..), Kind, Show2, UN, type (+->))
import Proarrow.Object (SomeOf (..), pattern Objs)
import Proarrow.Optic.Iso ()
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Representable (Rep)
import Proarrow.Tools.HypergraphRewrite (Rule, withSortParameters)
import Proarrow.Tools.HypergraphRewrite.Laws (Direction (..), subgraphRuleWithDirection)
import Proarrow.Tools.Laws (Equation, Labelled (..), LawBody, Laws (..), ProEquation (..), lawName, withSides)

-- | Named generators with arbitrary free-object endpoints, including compound
-- objects. Unlike 'Emb', these are not restricted to embedded base objects.
type NamedArrows :: Kind -> Constraint
class (CategoryOf k) => NamedArrows k where
  namedArrow :: (Ob (a :: k), Ob b) => String -> a ~> b

instance (NamedArrows `Elem` cs) => HasStructure cs p NamedArrows where
  data Struct NamedArrows a b where
    NamedArrow :: (Ob a, Ob b) => String -> Struct NamedArrows a b
  sameStructure (NamedArrow x) (NamedArrow y) = x P.== y
  foldStructure @f _ (NamedArrow @a @b name) = P.pure P.$ withLowerOb @f @a (withLowerOb @f @b (namedArrow name))

instance Show (Struct NamedArrows a b) where
  show (NamedArrow name) = show name

instance (NamedArrows `Elem` cs) => NamedArrows (FREE cs p) where
  namedArrow name = St (NamedArrow name) Nil

-- Discrete object shapes, restricted to those with runtime type evidence.
type data FREE_SHAPE = FO Type
instance CategoryOf FREE_SHAPE where
  type (~>) = (:~:)
  type Ob a = Any a

-- | Discrete sorts for reflected free objects.
type FREE_OB = SUBCAT (Typeable :: FREE_SHAPE -> Constraint)

-- | One wire carrying the exact source object, including its syntax category.
type FreeWire :: forall {k} {cs} {p :: CAT k} {l}. FREE cs p -> OPENHG FREE_OB l
type FreeWire a = Wires '[SUB (FO (Proxy a))]

-- | A structural operation distinguished by its signature's position in @cs@.
-- Child arrows do not participate in equality; their graph connections do.
type StructureBox :: [Kind -> Constraint] -> Type
data StructureBox cs where
  StructureBox :: (HasStructure cs p c) => Struct c (a :: FREE cs p) b -> String -> StructureBox cs

instance Eq (StructureBox cs) where
  StructureBox (s :: Struct c a b) _ == StructureBox (t :: Struct d x y) _ =
    case sameElem (elemEvidence @c @cs) (elemEvidence @d @cs) of
      Just Refl -> sameStructure s t
      Nothing -> False
instance Show (StructureBox cs) where
  show (StructureBox _ rendered) = rendered

data Building cs l = Building Int [SomeSort FREE_OB] [Box (Either (StructureBox cs) l) Int]

-- | Compile syntax, mapping base generators and named generators to labels.
-- Host and rule syntax must use the same @cs@ and @p@, so their reflected wire
-- sorts agree. Named generators can be mapped to parameters when compiling laws.
-- The base is discrete, and all structures must have instances on the source
-- free category.
fromFreeWith
  :: forall {k} {cs} {p :: CAT k} l (a :: FREE cs p) b
   . ( Typeable k
     , Typeable cs
     , Typeable p
     , forall (x :: k). (Ob x) => Typeable x
     , Discrete k
     , All cs (FREE cs p)
     , Show2 p
     , NamedArrows `Elem` cs
     )
  => (forall x y. (Ob x, Ob y) => p x y -> l)
  -> (String -> l)
  -> Free a b
  -> (FreeWire a :: OPENHG FREE_OB (Either (StructureBox cs) l)) ~> FreeWire b
fromFreeWith generator named term@Objs =
  withTypeableFreeOb @a $
    withTypeableFreeOb @b $
      let ((input, output), Building _ nodes boxes) = runState build (Building 0 [] [])
      in unsafeOpenHypergraph (reverse nodes) [input] [output] (reverse boxes)
  where
    build = do
      input <- fresh @a
      output <- go input term
      pure (input, output)

    fresh :: forall (x :: FREE cs p). (Ob x) => State (Building cs l) Int
    fresh = withTypeableFreeOb @x $ do
      Building next nodes boxes <- get
      put (Building (next + 1) (Some @(SUB (FO (Proxy x))) : nodes) boxes)
      pure next

    emit boxLabel inputs outputs = do
      Building next nodes boxes <- get
      put (Building next nodes (Box boxLabel inputs outputs : boxes))

    go :: forall (x :: FREE cs p) y. Int -> Free x y -> State (Building cs l) Int
    go input Nil = pure input
    go input (Emb p previous) = do
      mid <- go input previous
      output <- fresh @y
      emit (Right (generator p)) [mid] [output]
      pure output
    go input (St @c s previous) = do
      mid <- go input previous
      output <- fresh @y
      case sameElem (elemEvidence @c @cs) (elemEvidence @NamedArrows @cs) of
        Just Refl -> case s of
          NamedArrow name -> emit (Right (named name)) [mid] [output]
        Nothing -> do
          children <- traverse child (structureChildren s)
          -- Render references to children without expanding their syntax in the label.
          let rendered =
                fromAll @c @cs @(FREE cs p) $
                  show
                    ( runIdentity
                        ( foldStructure @_ @_ @_ @_ @(Rep (Embed :: k +-> FREE cs p))
                            (\Objs -> Identity (namedArrow "_"))
                            s
                        )
                    )
          emit
            (Left (StructureBox s rendered))
            (mid : map snd children)
            (output : map fst children)
      pure output

    child :: StructureChild cs p -> State (Building cs l) (Int, Int)
    child (StructureChild (f@Objs :: Free x y)) = do
      input <- fresh @x
      output <- go input f
      pure (input, output)

-- The five law objects are embedded symbolic objects. They may match any free
-- object, including a whole product or coproduct, in a concrete host syntax.
type data OBJECT_NAMES = OBJECT_NAME Symbol
instance CategoryOf OBJECT_NAMES where
  type (~>) = (:~:)
  type Ob a = Any a

type OBJECT_VARIABLES = SUBCAT (Typeable :: OBJECT_NAMES -> Constraint)
type ObjectQuiver = InitialProfunctor :: CAT OBJECT_VARIABLES
type ObjectSyntax :: [Kind -> Constraint] -> Kind
type ObjectSyntax cs = FREE cs ObjectQuiver

type ObjectVariable :: forall cs. Symbol -> ObjectSyntax cs
type ObjectVariable name = EMB (SUB (OBJECT_NAME name))

instance Labelled (ObjectSyntax cs) where
  label _ f = f

-- | Compile a named law with object variables and whole-arrow parameters.
-- One rule handles every instantiation of its five object variables, including
-- compound objects. Repeated variables must have the same object shape. Named
-- arrows capture connected subdiagrams with their own input and output, including
-- anchored identities. Repeated names require boundary-preserving graph isomorphism;
-- substitution does not compare diagrams modulo other laws. Complete matches
-- contain at least one box, and identical replacements are skipped.
freeLawRule
  :: forall laws cs a
   . (Laws laws, Typeable cs, All cs (ObjectSyntax cs), All laws (ObjectSyntax cs), NamedArrows `Elem` cs, Eq a)
  => String -> Either String (Rule FREE_OB (Either (StructureBox cs) a))
freeLawRule name = freeLawRuleWithDirection @laws @cs name LeftToRight

-- | Like 'freeLawRule', with an explicit orientation. Arrow parameters on the
-- right must occur on the left; an unbound right-side object rejects a match.
freeLawRuleWithDirection
  :: forall laws cs a
   . (Laws laws, Typeable cs, All cs (ObjectSyntax cs), All laws (ObjectSyntax cs), NamedArrows `Elem` cs, Eq a)
  => String -> Direction -> Either String (Rule FREE_OB (Either (StructureBox cs) a))
freeLawRuleWithDirection name direction =
  withSortParameters (matchObjectSorts @cs)
    <$> subgraphRuleWithDirection @laws name direction (either (Left P.. Left) Right) (objectLaw @laws @cs)

-- | Compile all laws with 'freeLawRule''s object and whole-arrow parameters,
-- retaining their names for a shared 'Proarrow.Tools.HypergraphRewrite.compileRules'.
--
-- >>> import Proarrow.Limit.BinaryProduct (HasBinaryProducts)
-- >>> type ProductStructures = '[NamedArrows, HasBinaryProducts]
-- >>> fmap (map fst) (freeLawRules @'[HasBinaryProducts] @ProductStructures @String)
-- Right ["fst","snd","pairing naturality","pairing the projections","pairing uniqueness"]
freeLawRules
  :: forall laws cs a
   . (Laws laws, Typeable cs, All cs (ObjectSyntax cs), All laws (ObjectSyntax cs), NamedArrows `Elem` cs, Eq a)
  => Either String [(String, Rule FREE_OB (Either (StructureBox cs) a))]
freeLawRules =
  traverse (\law -> (lawName law,) <$> freeLawRule @laws @cs (lawName law)) (laws @laws)

objectLaw
  :: forall laws cs
   . (Typeable cs, All cs (ObjectSyntax cs), All laws (ObjectSyntax cs), NamedArrows `Elem` cs)
  => LawBody laws -> Equation (OPENHG FREE_OB (Either (StructureBox cs) String))
objectLaw body =
  withSides
    ( runIdentity
        ( body
            @(ObjectVariable @cs "a")
            @(ObjectVariable @cs "b")
            @(ObjectVariable @cs "c")
            @(ObjectVariable @cs "d")
            @(ObjectVariable @cs "e")
            (\name -> Identity (namedArrow name))
        )
    )
    (\lhs rhs -> fromFreeWith (\case {}) P.id lhs :=: fromFreeWith (\case {}) P.id rhs)

objectType :: SomeSort FREE_OB -> Maybe SomeTypeRep
objectType (Some @x) = case typeRep @(UN SUB x) of
  App outer (App proxy a)
    | typeRepTyCon outer == typeRepTyCon (typeRep @(FO ()))
    , typeRepTyCon proxy == typeRepTyCon (typeRep @(Proxy ())) ->
        Just (SomeTypeRep a)
  _ -> Nothing

objectSort :: SomeTypeRep -> SomeSort FREE_OB
objectSort (SomeTypeRep (rep :: TypeRep a)) =
  withTypeable (typeRepKind rep) $ withTypeable rep $ Some @(SUB (FO (Proxy a)))

-- Match one-way: host objects are ground terms, even if their names happen to
-- look like variables. Kind and quiver substitutions keep every result in the
-- host's source category; the structure list must remain the same.
matchObjectSorts
  :: forall (cs :: [Kind -> Constraint])
   . (Typeable cs)
  => [SomeSort FREE_OB] -> [SomeSort FREE_OB] -> [SomeSort FREE_OB] -> Maybe [SomeSort FREE_OB]
matchObjectSorts patterns actual replacement = do
  templates <- traverse objectType patterns
  objects <- traverse objectType actual
  rhs <- traverse objectType replacement
  unless (length templates == length objects) Nothing
  first <- case objects of
    x : _ -> Just x
    [] -> Nothing
  (hostKind, hostBase, hostQuiver) <- sourceContext first
  unless (all ((== hostKind) P.. objectKind) objects) Nothing
  let context =
        M.fromList
          [ (SomeTypeRep (typeRep @(ObjectSyntax cs)), hostKind)
          , (SomeTypeRep (typeRep @OBJECT_VARIABLES), hostBase)
          , (SomeTypeRep (typeRep @ObjectQuiver), hostQuiver)
          ]
  bindings <- foldM (\env (template, object) -> unify env template object) context (zip templates objects)
  specialised <- traverse (substitute bindings) rhs
  unless (all ((== hostKind) P.. objectKind) specialised) Nothing
  pure (map objectSort specialised)
  where
    variables =
      [ SomeTypeRep (typeRep @(ObjectVariable @cs "a"))
      , SomeTypeRep (typeRep @(ObjectVariable @cs "b"))
      , SomeTypeRep (typeRep @(ObjectVariable @cs "c"))
      , SomeTypeRep (typeRep @(ObjectVariable @cs "d"))
      , SomeTypeRep (typeRep @(ObjectVariable @cs "e"))
      ]
    objectKind (SomeTypeRep rep) = SomeTypeRep (typeRepKind rep)
    sourceContext (SomeTypeRep rep) = case typeRepKind rep of
      kind@(App (App (Con' constructor [base]) structures) quiver)
        | constructor == typeRepTyCon (typeRep @(ObjectSyntax '[]))
        , SomeTypeRep structures == SomeTypeRep (typeRep @cs) ->
            Just (SomeTypeRep kind, base, SomeTypeRep quiver)
      _ -> Nothing

    unify env template object
      | Just expected <- M.lookup template env = if expected == object then Just env else Nothing
      | template `elem` variables = Just (M.insert template object env)
      | template == object = Just env
    unify env (SomeTypeRep (App f x)) (SomeTypeRep (App g y)) =
      unify env (SomeTypeRep f) (SomeTypeRep g) >>= \env' -> unify env' (SomeTypeRep x) (SomeTypeRep y)
    unify env (SomeTypeRep (Con' c ks)) (SomeTypeRep (Con' d ls))
      | c == d, length ks == length ls = foldM (\e (a, b) -> unify e a b) env (zip ks ls)
    unify _ _ _ = Nothing

    substitute env template
      | Just object <- M.lookup template env = Just object
      | template `elem` variables = Nothing
    substitute env (SomeTypeRep (App f x)) = do
      f' <- substitute env (SomeTypeRep f)
      x' <- substitute env (SomeTypeRep x)
      applyType f' x'
    substitute env original@(SomeTypeRep (Con' c kinds)) = do
      kinds' <- traverse (substitute env) kinds
      -- The constructor and arity come from a compiler-produced TypeRep. Only
      -- its source-category kind arguments change; explicit applications below
      -- check their argument kinds before constructing a reflected sort.
      pure (if kinds' == kinds then original else SomeTypeRep (mkTrCon c kinds'))

applyType :: SomeTypeRep -> SomeTypeRep -> Maybe SomeTypeRep
applyType (SomeTypeRep f) (SomeTypeRep x) = case typeRepKind f of
  Fun argument result -> case eqTypeRep (typeRepKind result) (typeRep @Type) of
    Just HRefl -> case eqTypeRep argument (typeRepKind x) of
      Just HRefl -> Just (SomeTypeRep (App f x))
      Nothing -> Nothing
    Nothing -> Nothing
  _ -> Nothing
